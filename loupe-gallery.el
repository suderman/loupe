;;; loupe-gallery.el --- Square-tile image gallery for loupe -*- lexical-binding: t; -*-

;; Copyright (C) 2026 Jon Suderman

;; Author: Jon Suderman
;; URL: https://github.com/suderman/loupe
;; SPDX-License-Identifier: GPL-3.0-or-later

;; This file is not part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:
;; `loupe-gallery' shows a directory's images as a grid of square tiles
;; sized to the window.  Rows are text, and each thumbnail loads only when
;; redisplay first shows its row, so a camera folder with thousands of
;; photos opens at once and scrolls by touch like any buffer.  Thumbnails
;; share the freedesktop cache with Image-Dired and desktop file managers.
;; Images open in Image mode, where paging and swiping follow the
;; gallery's order and `q' comes back.

;;; Code:

(require 'cl-lib)
(require 'subr-x)
(require 'image-dired)
(require 'image-file)
(require 'jit-lock)
(require 'loupe)

(declare-function touch-screen-inhibit-drag "touch-screen")

(defcustom loupe-gallery-tile-width 260
  "Approximate tile width in pixels; the window decides the column count."
  :type 'natnum
  :group 'loupe)

(defcustom loupe-gallery-gap 8
  "Pixels between tiles."
  :type 'natnum
  :group 'loupe)

(defface loupe-gallery-tile
  '((((background dark)) :background "gray20")
    (t :background "gray85"))
  "Face of a tile whose thumbnail has not loaded yet."
  :group 'loupe)

;;;; State

(defvar-local loupe-gallery--files []
  "Image files in gallery order.")

(defvar-local loupe-gallery--cells []
  "Buffer position of each file's thumbnail.")

(defvar-local loupe-gallery--cell nil
  "Thumbnail cell size in pixels.")

(defvar-local loupe-gallery--columns nil
  "Number of columns chosen with `+' and `-', or nil to fit the window.")

(defvar-local loupe-gallery--column-count 1
  "Number of columns in the current layout.")

(defvar-local loupe-gallery--layout-width nil
  "Window width the grid was laid out for.")

(defvar-local loupe-gallery--scan nil
  "Function returning the gallery's files in listing order.")

(defvar-local loupe-gallery--newest-first nil
  "Non-nil to show the newest images first.")

(defvar-local loupe-gallery--marks nil
  "Marked files, as a hash table.")

(defvar-local loupe-gallery--shown-index 0
  "Index of the image last opened from the gallery.")

(defvar-local loupe-gallery--return nil
  "Window configuration to restore when the gallery closes.")

(defvar-local loupe-gallery--current-overlay nil
  "Overlay that frames the selected thumbnail.")

;;;; Files

(defun loupe-gallery--image-p (file)
  "Return non-nil if FILE is an image Emacs can show."
  (and (string-match-p (image-file-name-regexp) file)
       (file-regular-p file)))

(defun loupe-gallery--dired-files (buffer)
  "Return the top-level images listed in Dired BUFFER, in its order."
  (with-current-buffer buffer
    (let ((directory (file-name-as-directory (expand-file-name default-directory)))
          files)
      (save-excursion
        (goto-char (point-min))
        (while (not (eobp))
          (when-let* ((file (dired-get-filename nil t))
                      ((equal (file-name-directory file) directory))
                      ((loupe-gallery--image-p file)))
            (push file files))
          (forward-line 1)))
      (nreverse files))))

(defun loupe-gallery--directory-files (directory)
  "Return the images in DIRECTORY, by name."
  (seq-filter #'file-regular-p
              (directory-files directory t (image-file-name-regexp))))

(defun loupe-gallery--order (files)
  "Return FILES in the gallery's current order."
  (if (not loupe-gallery--newest-first)
      files
    (mapcar #'car
            (sort (mapcar (lambda (file)
                            (cons file (file-attribute-modification-time
                                        (file-attributes file))))
                          files)
                  (lambda (a b) (time-less-p (cdr b) (cdr a)))))))

;;;; Layout

(defun loupe-gallery--show-selected ()
  "Scroll so the selected thumbnail's row is the first one shown."
  (when-let* ((window (get-buffer-window nil t)))
    (set-window-start window (line-beginning-position) t)))

(defun loupe-gallery--layout (&optional index)
  "Lay out the grid for the gallery's window, selecting INDEX."
  (let* ((window (or (get-buffer-window nil t) (selected-window)))
         (width (- (nth 2 (window-inside-pixel-edges window))
                   (nth 0 (window-inside-pixel-edges window))))
         (gap loupe-gallery-gap)
         (columns (max 1 (or loupe-gallery--columns
                             (round (- width gap)
                                    (+ loupe-gallery-tile-width gap)))))
         (cell (max 32 (/ (- width (* (1+ columns) gap)) columns)))
         (left (max 0 (/ (- width (* columns cell) (* (1- columns) gap)) 2)))
         (files loupe-gallery--files)
         (cells (make-vector (length files) nil))
         (index (or index (loupe-gallery--index) 0))
         (inhibit-read-only t))
    ;; Thumbnails are cached at 256 or 512 pixels; use the smallest that fills a tile.
    (setq-local image-dired-thumbnail-storage
                (if (> cell 256) 'standard-x-large 'standard-large))
    (setq loupe-gallery--cell cell
          loupe-gallery--column-count columns
          loupe-gallery--layout-width width)
    (with-silent-modifications
      (erase-buffer)
      (dotimes (i (length files))
        (when (zerop (% i columns))
          (unless (zerop i) (insert (propertize "\n" 'pointer 'arrow)))
          ;; A gap taller than a tile, centred on the baseline like the
          ;; tiles, so every row has the same height and spacing.
          (insert (propertize " " 'display
                              `(space :width (,left) :height (,(+ cell gap))
                                      :ascent 50)
                              'pointer 'arrow)))
        (unless (zerop (% i columns))
          (insert (propertize " " 'display `(space :width (,gap)) 'pointer 'arrow)))
        (aset cells i (point))
        (insert (propertize " "
                            'loupe-gallery-index i
                            'display `(space :width (,cell) :height (,cell) :ascent 50)
                            'face 'loupe-gallery-tile
                            'pointer 'hand
                            'help-echo (abbreviate-file-name (aref files i)))))
      (insert (propertize "\n" 'pointer 'arrow)))
    (setq loupe-gallery--cells cells)
    (when (> (length cells) 0)
      (goto-char (aref cells (min index (1- (length cells))))))
    (loupe-gallery--show-marks)
    (loupe-gallery--select)))

(defun loupe-gallery--refit (window)
  "Lay out again when WINDOW's width changed."
  (with-current-buffer (window-buffer window)
    (when (and (derived-mode-p 'loupe-gallery-mode)
               (not (eql loupe-gallery--layout-width
                         (- (nth 2 (window-inside-pixel-edges window))
                            (nth 0 (window-inside-pixel-edges window))))))
      (loupe-gallery--layout))))

;;;; Thumbnails

(defvar loupe-gallery--queue nil
  "Thumbnails to make, most recently requested first, as (BUFFER INDEX).")

(defvar loupe-gallery--batches nil
  "Thumbnails being made, a list per process.
Each entry is (THUMBNAIL BUFFER INDEX FILE START).")

(defvar loupe-gallery--timer nil
  "Timer that watches for finished thumbnails.")

(defconst loupe-gallery--queue-limit 48
  "Most thumbnails to keep waiting; older requests have scrolled away.")

(defconst loupe-gallery--batch-size 6
  "Thumbnails one process makes.")

(defun loupe-gallery--thumbnail (file &optional storage)
  "Return FILE's current cached thumbnail, or nil.
STORAGE overrides `image-dired-thumbnail-storage'."
  (let ((thumbnail (let ((image-dired-thumbnail-storage
                          (or storage image-dired-thumbnail-storage)))
                     (image-dired-thumb-name file))))
    (and (file-exists-p thumbnail)
         (not (file-newer-than-file-p file thumbnail))
         thumbnail)))

(defun loupe-gallery--fontify (start end)
  "Load the thumbnails between START and END as redisplay reaches them."
  (let ((pos start))
    (while (and pos (< pos end))
      (when-let* ((index (get-text-property pos 'loupe-gallery-index))
                  ((not (get-text-property pos 'loupe-gallery-loading))))
        (if-let* ((thumbnail (loupe-gallery--thumbnail
                              (aref loupe-gallery--files index))))
            (loupe-gallery--place index thumbnail)
          ;; Show the other cached size until this one is made.
          (when-let* ((other (loupe-gallery--thumbnail
                              (aref loupe-gallery--files index)
                              (if (eq image-dired-thumbnail-storage 'standard-large)
                                  'standard-x-large
                                'standard-large))))
            (loupe-gallery--place index other))
          (put-text-property pos (1+ pos) 'loupe-gallery-loading t)
          (push (list (current-buffer) index) loupe-gallery--queue)
          (loupe-gallery--trim-queue)
          (run-at-time 0 nil #'loupe-gallery--run)))
      (setq pos (next-single-property-change pos 'loupe-gallery-index nil end)))))

(defun loupe-gallery--place (index thumbnail)
  "Show THUMBNAIL in cell INDEX, scaled to cover its square tile and cropped."
  (let* ((pos (aref loupe-gallery--cells index))
         (cell loupe-gallery--cell)
         (probe (create-image thumbnail nil nil :scale 1))
         (size (image-size probe t))
         (width (max 1 (round (car size))))
         (height (max 1 (round (cdr size))))
         (factor (/ cell (float (min width height))))
         (scaled-width (max cell (round (* width factor))))
         (scaled-height (max cell (round (* height factor))))
         (spec (create-image thumbnail nil nil :scale 1
                             :width scaled-width :height scaled-height)))
    (image-flush probe)
    (with-silent-modifications
      (add-text-properties
       pos (1+ pos)
       `(display ((slice ,(/ (- scaled-width cell) 2) ,(/ (- scaled-height cell) 2)
                         ,cell ,cell)
                  ,spec)
                 loupe-gallery-loading t)))))

(defun loupe-gallery--forget (buffer index)
  "Let cell INDEX of gallery BUFFER ask for its thumbnail again when shown."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (when (< index (length loupe-gallery--cells))
        (let ((pos (aref loupe-gallery--cells index)))
          (with-silent-modifications
            (remove-text-properties pos (1+ pos)
                                    '(loupe-gallery-loading nil fontified nil))))))))

(defun loupe-gallery--trim-queue ()
  "Forget the oldest requests beyond `loupe-gallery--queue-limit'.
Their rows have most likely scrolled away; redisplay asks again if they return."
  (when-let* ((tail (nthcdr (1- loupe-gallery--queue-limit) loupe-gallery--queue)))
    (pcase-dolist (`(,buffer ,index) (cdr tail))
      (loupe-gallery--forget buffer index))
    (setcdr tail nil)))

(defun loupe-gallery--converter-options (size)
  "Return Image-Dired's thumbnail options for SIZE, decoding faster.
Camera photos often keep their rotation in Exif only, so apply it too."
  (let ((options (copy-sequence image-dired-cmd-create-standard-thumbnail-options)))
    (unless (member "-auto-orient" options)
      (when-let* ((input (member "%f[0]" options)))
        (setcdr input (cons "-auto-orient" (cdr input)))))
    (if (equal (car options) "convert")
        ;; GraphicsMagick's subcommand must come first.
        options
      (append (list "-define" (format "jpeg:size=%dx%d" (* 2 size) (* 2 size)))
              options))))

(defun loupe-gallery--command (file thumbnail)
  "Return a shell command that writes FILE's THUMBNAIL whole or not at all."
  (let* ((partial (concat thumbnail ".part"))
         (size (if (eq image-dired-thumbnail-storage 'standard-x-large) 512 256))
         (spec `((?s . ,size) (?w . ,size) (?h . ,size)
                 (?m . ,(format-time-string
                         "%s" (file-attribute-modification-time (file-attributes file))))
                 (?f . ,file) (?u . ,file) (?t . ,partial))))
    (format "%s && mv -f %s %s"
            (mapconcat #'shell-quote-argument
                       (cons (if (executable-find "magick")
                                 "magick"
                               image-dired-cmd-create-thumbnail-program)
                             (mapcar (lambda (option) (format-spec option spec))
                                     (loupe-gallery--converter-options size)))
                       " ")
            (shell-quote-argument partial)
            (shell-quote-argument thumbnail))))

(defun loupe-gallery--run ()
  "Start making queued thumbnails, newest request first, a batch per process."
  (let ((limit (min 3 (max 1 (/ (num-processors) 2)))))
    (while (and loupe-gallery--queue
                (< (length loupe-gallery--batches) limit))
      (let (batch commands)
        (while (and loupe-gallery--queue
                    (< (length batch) loupe-gallery--batch-size))
          (pcase-let ((`(,buffer ,index) (pop loupe-gallery--queue)))
            (when (buffer-live-p buffer)
              (with-current-buffer buffer
                (when (< index (length loupe-gallery--files))
                  (let* ((file (aref loupe-gallery--files index))
                         (thumbnail (image-dired-thumb-name file)))
                    (make-directory (file-name-directory thumbnail) t)
                    (push (list thumbnail buffer index file (float-time)) batch)
                    (push (loupe-gallery--command file thumbnail) commands)))))))
        (when batch
          ;; The thumbnail standard wants files only their owner can read.
          (loupe-run-shell
           (concat "umask 077; " (string-join (nreverse commands) "; ")))
          (push batch loupe-gallery--batches)))))
  (when (and loupe-gallery--batches (not (timerp loupe-gallery--timer)))
    (setq loupe-gallery--timer
          (run-with-timer 0.3 0.3 #'loupe-gallery--poll))))

(defun loupe-gallery--poll ()
  "Show thumbnails that have appeared, and start more."
  (let ((now (float-time)))
    (setq loupe-gallery--batches
          (delq nil
                (mapcar
                 (lambda (batch)
                   (seq-remove
                    (pcase-lambda (`(,thumbnail ,buffer ,index ,file ,start))
                      (cond
                       ((file-exists-p thumbnail)
                        (when (buffer-live-p buffer)
                          (with-current-buffer buffer
                            (when (and (< index (length loupe-gallery--files))
                                       (equal file (aref loupe-gallery--files index)))
                              (loupe-gallery--place index thumbnail))))
                        t)
                       ;; A file the converter cannot read never appears.
                       ((> (- now start) 30) t)))
                    batch))
                 loupe-gallery--batches))))
  (loupe-gallery--run)
  (unless loupe-gallery--batches
    (cancel-timer loupe-gallery--timer)
    (setq loupe-gallery--timer nil)))

;;;; Selection and marks

(defun loupe-gallery--index (&optional pos)
  "Return the image index at POS, or the nearest one before it."
  (let ((pos (or pos (point))))
    (or (get-text-property pos 'loupe-gallery-index)
        (when-let* ((next (next-single-property-change
                           pos 'loupe-gallery-index nil (line-end-position))))
          (get-text-property next 'loupe-gallery-index))
        (when-let* ((previous (previous-single-property-change
                               pos 'loupe-gallery-index)))
          (get-text-property (max (point-min) (1- previous)) 'loupe-gallery-index)))))

(defun loupe-gallery--select ()
  "Snap point to a thumbnail and frame it; a marked one gets a thicker frame."
  (when-let* ((index (loupe-gallery--index)))
    (goto-char (aref loupe-gallery--cells index))
    (unless (overlayp loupe-gallery--current-overlay)
      (setq loupe-gallery--current-overlay (make-overlay 1 1))
      (overlay-put loupe-gallery--current-overlay 'priority 10))
    (let ((color (or (face-foreground 'cursor nil t)
                     (face-background 'cursor nil t)
                     "gray50"))
          (width (if (gethash (aref loupe-gallery--files index)
                              loupe-gallery--marks)
                     -10 -4)))
      (overlay-put loupe-gallery--current-overlay 'face
                   `(:box (:line-width (,width . ,width) :color ,color))))
    (move-overlay loupe-gallery--current-overlay (point) (1+ (point)))))

(defun loupe-gallery--show-marks ()
  "Frame every marked thumbnail."
  (remove-overlays (point-min) (point-max) 'loupe-gallery-mark t)
  (let ((color (or (face-foreground 'success nil t) "gray70")))
    (dotimes (index (length loupe-gallery--files))
      (when (gethash (aref loupe-gallery--files index) loupe-gallery--marks)
        (let* ((pos (aref loupe-gallery--cells index))
               (overlay (make-overlay pos (1+ pos))))
          (overlay-put overlay 'loupe-gallery-mark t)
          (overlay-put overlay 'face `(:box (:line-width (-10 . -10) :color ,color))))))))

(defun loupe-gallery--current-file ()
  "Return the selected image file."
  (when-let* ((index (loupe-gallery--index)))
    (aref loupe-gallery--files index)))

(defun loupe-gallery--targets ()
  "Return the marked files, or the selected one."
  (or (seq-filter (lambda (file) (gethash file loupe-gallery--marks))
                  loupe-gallery--files)
      (when-let* ((file (loupe-gallery--current-file)))
        (list file))))

;;;; Commands

;;;###autoload
(defun loupe-gallery (&optional directory)
  "Show the images of the current directory as a thumbnail gallery.
From Dired or Dirvish, use the images in the listing's order; from an image,
those in its DIRECTORY.  Start on the image at point or the one shown."
  (interactive)
  (unless (display-graphic-p)
    (user-error "The gallery needs a graphical frame"))
  (let* ((source (current-buffer))
         (dired (derived-mode-p 'dired-mode))
         (selected (cond (dired (dired-get-filename nil t))
                         ((derived-mode-p 'image-mode) buffer-file-name)))
         (directory (file-name-as-directory
                     (expand-file-name (or directory default-directory))))
         (scan (if dired
                   (lambda () (when (buffer-live-p source)
                                (with-current-buffer source (revert-buffer nil t))
                                (loupe-gallery--dired-files source)))
                 (lambda () (loupe-gallery--directory-files directory))))
         (files (funcall scan)))
    (unless files
      (user-error "No images in %s" (abbreviate-file-name directory)))
    (let ((configuration (current-window-configuration))
          (gallery (get-buffer-create
                    (format "*gallery %s*" (abbreviate-file-name directory)))))
      (with-current-buffer gallery
        (loupe-gallery-mode)
        (setq default-directory directory
              loupe-gallery--scan scan
              loupe-gallery--files (vconcat (loupe-gallery--order files))
              loupe-gallery--return configuration))
      ;; Dirvish's panes are dedicated; open over the whole frame.
      (let ((ignore-window-parameters t))
        (delete-other-windows))
      (set-window-dedicated-p nil nil)
      (switch-to-buffer gallery nil t)
      (loupe-gallery--layout (or (seq-position loupe-gallery--files selected) 0))
      (loupe-gallery--show-selected))))

(defun loupe-gallery-quit ()
  "Close the gallery and restore the windows it replaced."
  (interactive)
  (let ((gallery (current-buffer))
        (configuration loupe-gallery--return)
        (file (loupe-gallery--current-file)))
    (if configuration
        (set-window-configuration configuration)
      (quit-window))
    (let ((window (selected-window)))
      (with-current-buffer (window-buffer window)
        (when (and file (derived-mode-p 'dired-mode) (dired-goto-file file))
          (set-window-point window (point)))))
    (kill-buffer gallery)))

(defvar-local loupe-gallery--opened nil
  "Non-nil in an image buffer the gallery opened, and so may close.")

(defun loupe-gallery--close (buffer)
  "Kill image BUFFER if the gallery opened it."
  (when (and (buffer-live-p buffer)
             (buffer-local-value 'loupe-gallery--opened buffer))
    (kill-buffer buffer)))

(defun loupe-gallery--visit (gallery index)
  "Show image INDEX of GALLERY in the selected window.
Close the image it replaces if the gallery opened that one."
  (with-current-buffer gallery
    (setq loupe-gallery--shown-index index))
  (let* ((previous (current-buffer))
         (file (aref (buffer-local-value 'loupe-gallery--files gallery) index))
         (existing (find-buffer-visiting file)))
    (switch-to-buffer (or existing (find-file-noselect file)))
    (unless existing
      (setq loupe-gallery--opened t))
    (setq-local loupe-step-function
                (lambda (n) (loupe-gallery--step gallery n))
                loupe-quit-function
                (lambda () (loupe-gallery--back gallery)))
    (unless (eq previous (current-buffer))
      (loupe-gallery--close previous))))

(defun loupe-gallery--step (gallery n)
  "Replace the shown image with the one N places after it in GALLERY."
  (unless (buffer-live-p gallery)
    (user-error "The gallery is closed"))
  (let* ((index (buffer-local-value 'loupe-gallery--shown-index gallery))
         (count (length (buffer-local-value 'loupe-gallery--files gallery)))
         (next (+ index n)))
    (unless (< -1 next count)
      (user-error (if (< n 0) "First image" "Last image")))
    (loupe-gallery--visit gallery next)))

(defun loupe-gallery--back (gallery)
  "Return from an image to GALLERY."
  (let ((image (current-buffer)))
    (if (not (buffer-live-p gallery))
        (quit-window)
      (switch-to-buffer gallery)
      (goto-char (aref loupe-gallery--cells loupe-gallery--shown-index))
      (loupe-gallery--select)
      (unless (pos-visible-in-window-p)
        (loupe-gallery--show-selected)))
    (loupe-gallery--close image)))

(defun loupe-gallery-open ()
  "Open the selected image."
  (interactive)
  (when-let* ((index (loupe-gallery--index)))
    (loupe-gallery--visit (current-buffer) index)))

(defun loupe-gallery-mouse-open (event)
  "Open the image clicked in EVENT."
  (interactive "e")
  (let ((posn (event-start event)))
    (with-selected-window (posn-window posn)
      (when-let* ((pos (posn-point posn))
                  ((get-text-property pos 'loupe-gallery-index)))
        (goto-char pos)
        (loupe-gallery-open)))))

(defun loupe-gallery-mouse-press ()
  "Ignore a press in the gallery; the click selects or opens."
  (interactive))

;; No region dragging, which would select every tile as whitespace, and a
;; touch on Android still scrolls.
(put 'loupe-gallery-mouse-press 'ignored-mouse-command t)

(defun loupe-gallery-mouse-select (event)
  "Select the image clicked in EVENT; on Android open it."
  (interactive "e")
  (if (featurep 'android)
      (loupe-gallery-mouse-open event)
    (mouse-set-point event)
    (loupe-gallery--select)))

(defun loupe-gallery-hold (event)
  "Mark or unmark the image held down in touch EVENT."
  (interactive "e")
  (let ((posn (cadr event)))
    (with-selected-window (posn-window posn)
      (when-let* ((pos (posn-point posn))
                  ((get-text-property pos 'loupe-gallery-index)))
        (when (fboundp 'touch-screen-inhibit-drag)
          (touch-screen-inhibit-drag))
        (goto-char pos)
        (loupe-gallery-toggle-mark t)))))

(defun loupe-gallery--move (n)
  "Select the image N places away, staying in range."
  (when-let* ((index (loupe-gallery--index)))
    (goto-char (aref loupe-gallery--cells
                     (max 0 (min (1- (length loupe-gallery--cells)) (+ index n)))))
    (loupe-gallery--select)))

(defun loupe-gallery-left () "Select the previous image." (interactive) (loupe-gallery--move -1))
(defun loupe-gallery-right () "Select the next image." (interactive) (loupe-gallery--move 1))
(defun loupe-gallery-up () "Select the image above." (interactive)
       (loupe-gallery--move (- loupe-gallery--column-count)))
(defun loupe-gallery-down () "Select the image below." (interactive)
       (loupe-gallery--move loupe-gallery--column-count))

(defun loupe-gallery-toggle-mark (&optional stay)
  "Mark or unmark the selected image, then select the next unless STAY."
  (interactive)
  (when-let* ((file (loupe-gallery--current-file)))
    (if (gethash file loupe-gallery--marks)
        (remhash file loupe-gallery--marks)
      (puthash file t loupe-gallery--marks))
    (loupe-gallery--show-marks)
    (unless stay (loupe-gallery--move 1))
    (force-mode-line-update)))

(defun loupe-gallery-unmark-all ()
  "Unmark every image."
  (interactive)
  (clrhash loupe-gallery--marks)
  (loupe-gallery--show-marks)
  (force-mode-line-update))

(defun loupe-gallery--reload (files)
  "Show FILES, keeping the selection near where it was."
  (let ((index (or (loupe-gallery--index) 0)))
    (setq loupe-gallery--files (vconcat (loupe-gallery--order files)))
    (maphash (lambda (file _)
               (unless (seq-contains-p loupe-gallery--files file)
                 (remhash file loupe-gallery--marks)))
             loupe-gallery--marks)
    (if (zerop (length loupe-gallery--files))
        (progn (loupe-gallery-quit)
               (message "No images remain"))
      (loupe-gallery--layout (min index (1- (length loupe-gallery--files)))))))

(defun loupe-gallery-refresh ()
  "Rescan the directory and rebuild the gallery."
  (interactive)
  (loupe-gallery--reload (funcall loupe-gallery--scan)))

(defun loupe-gallery-toggle-order ()
  "Switch between listing order and newest first."
  (interactive)
  (let ((file (loupe-gallery--current-file)))
    (setq loupe-gallery--newest-first (not loupe-gallery--newest-first))
    (setq loupe-gallery--files
          (vconcat (loupe-gallery--order (funcall loupe-gallery--scan))))
    (loupe-gallery--layout (or (seq-position loupe-gallery--files file) 0))
    (loupe-gallery--show-selected)
    (message (if loupe-gallery--newest-first "Newest first" "Listing order"))))

(defun loupe-gallery-delete ()
  "Delete the marked images, or the selected one, after confirmation."
  (interactive)
  (let ((files (loupe-gallery--targets)))
    (when (and files
               (yes-or-no-p (if (cdr files)
                                (format "Delete %d images? " (length files))
                              (format "Delete %s? " (file-name-nondirectory (car files))))))
      (dolist (file files)
        (when-let* ((buffer (find-buffer-visiting file)))
          (kill-buffer buffer))
        (delete-file file t))
      (loupe-gallery--reload
       (seq-remove (lambda (file) (member file files))
                   (append loupe-gallery--files nil)))
      (message "Deleted %d image%s" (length files) (if (cdr files) "s" "")))))

(defun loupe-gallery-larger ()
  "Show fewer, larger thumbnails."
  (interactive)
  (setq loupe-gallery--columns
        (max 1 (1- (or loupe-gallery--columns loupe-gallery--column-count))))
  (loupe-gallery--layout)
  (loupe-gallery--show-selected))

(defun loupe-gallery-smaller ()
  "Show more, smaller thumbnails."
  (interactive)
  (setq loupe-gallery--columns
        (1+ (or loupe-gallery--columns loupe-gallery--column-count)))
  (loupe-gallery--layout)
  (loupe-gallery--show-selected))

(defvar loupe-gallery--pinch-ready t
  "Non-nil while a pinch is near its starting spread and may take a step.")

(defun loupe-gallery-pinch (event)
  "Show one column fewer or more for each pinch EVENT gesture.
Spreading shows fewer, larger thumbnails, keeping the one under the fingers.
The fingers must come back near where they started before another step,
so one pinch never changes the grid twice."
  (interactive "e")
  (let* ((desktop (eq (car event) 'pinch))
         (posn (nth 1 event))
         (scale (if desktop (nth 4 event) (nth 2 event)))
         (window (posn-window posn)))
    (cond
     ((< (abs (- scale 1.0)) 0.08)
      (setq loupe-gallery--pinch-ready t))
     ((and loupe-gallery--pinch-ready
           (windowp window)
           (or (> scale 1.25) (< scale 0.8)))
      (setq loupe-gallery--pinch-ready nil)
      (with-selected-window window
        (let ((columns (+ loupe-gallery--column-count (if (> scale 1) -1 1))))
          (when (<= 1 columns 12)
            (setq loupe-gallery--columns columns)
            (loupe-gallery--layout
             (or (and (posn-point posn)
                      (get-text-property (posn-point posn) 'loupe-gallery-index))
                 (loupe-gallery--index)))
            (recenter))))))))

(defun loupe-gallery--header ()
  "Return the gallery's header line."
  (let ((marks (hash-table-count loupe-gallery--marks)))
    (concat (format " %d images" (length loupe-gallery--files))
            (if (> marks 0) (format ", %d marked" marks) "")
            (if loupe-gallery--newest-first ", newest first" "")
            "  " (abbreviate-file-name default-directory))))

(defvar-keymap loupe-gallery-mode-map
  :doc "Keys in the image gallery."
  "h" #'loupe-gallery-left
  "j" #'loupe-gallery-down
  "k" #'loupe-gallery-up
  "l" #'loupe-gallery-right
  "<left>" #'loupe-gallery-left
  "<down>" #'loupe-gallery-down
  "<up>" #'loupe-gallery-up
  "<right>" #'loupe-gallery-right
  "RET" #'loupe-gallery-open
  "o" #'loupe-gallery-open
  "m" #'loupe-gallery-toggle-mark
  "U" #'loupe-gallery-unmark-all
  "d" #'loupe-gallery-delete
  "s" #'loupe-gallery-toggle-order
  "g" #'loupe-gallery-refresh
  "+" #'loupe-gallery-larger
  "=" #'loupe-gallery-larger
  "-" #'loupe-gallery-smaller
  "q" #'loupe-gallery-quit
  "<down-mouse-1>" #'loupe-gallery-mouse-press
  "<double-down-mouse-1>" #'loupe-gallery-mouse-press
  "<mouse-1>" #'loupe-gallery-mouse-select
  "<double-mouse-1>" #'loupe-gallery-mouse-open
  "<touchscreen-hold>" #'loupe-gallery-hold
  "<touchscreen-pinch>" #'loupe-gallery-pinch
  "<pinch>" #'loupe-gallery-pinch
  "C-<wheel-up>" #'loupe-gallery-larger
  "C-<wheel-down>" #'loupe-gallery-smaller)

(define-derived-mode loupe-gallery-mode special-mode "Gallery"
  "Browse a directory's images as thumbnails."
  (setq-local cursor-type nil
              truncate-lines t
              loupe-gallery--marks (make-hash-table :test #'equal)
              header-line-format '(:eval (loupe-gallery--header))
              ;; Small chunks load only the rows redisplay shows.
              jit-lock-chunk-size 64)
  (jit-lock-register #'loupe-gallery--fontify)
  (add-hook 'post-command-hook #'loupe-gallery--select nil t)
  (add-hook 'window-size-change-functions #'loupe-gallery--refit nil t))

(provide 'loupe-gallery)
;;; loupe-gallery.el ends here
