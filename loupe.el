;;; loupe.el --- Pinch, pan, and swipe images and PDFs -*- lexical-binding: t; -*-

;; Copyright (C) 2026 Jon Suderman

;; Author: Jon Suderman
;; Version: 0.1.0
;; Package-Requires: ((emacs "30.1"))
;; Keywords: multimedia, mouse
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
;; `loupe-mode' turns Image mode, DocView, and PDF Tools into viewers you
;; can pinch, pan, and swipe by touch screen, touchpad, mouse, or keys.
;;
;; Emacs scales an image when it loads it, so each new zoom level costs a
;; full decode plus a scaling pass: on the Android port about 0.2 to 1 s
;; for a camera photo.  While fingers move, zooming therefore draws a
;; small proxy without smoothing, and draws the real image once they stop.
;; Panning only moves an image slice, which costs nothing.  An overlay in
;; the image's window draws the slice, centred, over Image mode's own
;; display property, which its commands keep reading.
;;
;; `loupe-gallery' in loupe-gallery.el shows a directory as thumbnails.

;;; Code:

(require 'cl-lib)
(require 'subr-x)
(require 'image-mode)
(require 'exif)

(defvar dired-movement-style)
(defvar doc-view-image-width)
(declare-function touch-screen-relative-xy "touch-screen" (posn window))
(declare-function doc-view-enlarge "doc-view" (factor))
(declare-function doc-view-next-page "doc-view" (&optional arg))
(declare-function doc-view-goto-page "doc-view" (page))
(declare-function doc-view-last-page-number "doc-view")
(declare-function pdf-view-enlarge "pdf-view" (factor &optional window))
(declare-function pdf-view-next-page "pdf-view" (&optional n window))
(declare-function pdf-view-redisplay "pdf-view" (&optional window))
(declare-function pdf-cache-number-of-pages "pdf-cache" (&optional buffer))
(autoload 'loupe-gallery "loupe-gallery" nil t)

(defgroup loupe nil
  "Pinch, pan, and swipe images and PDFs."
  :group 'image
  :prefix "loupe-")

(defcustom loupe-max-zoom 8.0
  "Largest zoom, relative to an image's fitted size."
  :type 'number)

(defcustom loupe-max-pixels 24000000
  "Largest zoomed image to hold in memory, in pixels.
Emacs keeps a zoomed image whole, about 8 bytes per pixel on Android."
  :type 'natnum)

(defcustom loupe-double-tap-zoom 2.5
  "Zoom a double tap or double click jumps to."
  :type 'number)

(defcustom loupe-proxy-size 1600
  "Longest edge, in pixels, of the rough copy drawn while zooming."
  :type 'natnum)

(defcustom loupe-proxy-min-bytes 1000000
  "Smallest image file worth a proxy; smaller files decode fast enough."
  :type 'natnum)

(defcustom loupe-proxy-limit 300
  "Number of proxies to keep in `loupe-proxy-directory'."
  :type 'natnum)

(defcustom loupe-proxy-directory
  (expand-file-name "loupe/" (or (getenv "XDG_CACHE_HOME") "~/.cache"))
  "Directory for the proxies drawn while zooming."
  :type 'directory)

(defcustom loupe-document-fit-width t
  "Non-nil to open DocView pages fitted to the window's width."
  :type 'boolean)

(defvar loupe-mode)
(defvar loupe-image-mode)

;;;; State

(defvar-local loupe--zoom 1.0
  "Zoom of this buffer's image relative to its fitted size.")

(defvar-local loupe--origin nil
  "Top-left corner of the window as (X . Y) pixels in the zoomed image.
Nil centres the image.")

(defvar-local loupe--shift 0
  "Pixels a sideways swipe has dragged the fitted image to the right.")

(defvar-local loupe--overlay nil
  "Overlay that draws this buffer's image in one window.")

(defvar-local loupe--shown nil
  "Zoomed image spec the overlay draws, as (KEY . SPEC), or nil at fit.")

(defvar-local loupe--geometry nil
  "Last drawn (X Y WIDTH HEIGHT): the window's corner in the image and its size.")

(defvar-local loupe-step-function nil
  "Function that visits the Nth next image, or nil for directory order.
A gallery sets it so that paging follows the gallery.")

(defvar-local loupe-quit-function nil
  "Function that leaves this image, or nil for `quit-window'.")

;;;; Drawing

(defun loupe--base ()
  "Return Image mode's own image spec in this buffer, or nil."
  (let ((spec (get-text-property (point-min) 'display)))
    (and (eq (car-safe spec) 'image) spec)))

(defun loupe--window ()
  "Return the window showing this buffer, preferring the selected one."
  (if (eq (window-buffer) (current-buffer))
      (selected-window)
    (get-buffer-window nil 'visible)))

(defun loupe--box (window)
  "Return WINDOW's text area as (WIDTH . HEIGHT) pixels."
  (let ((edges (window-inside-pixel-edges window)))
    (cons (- (nth 2 edges) (nth 0 edges))
          (- (nth 3 edges) (nth 1 edges)))))

(defun loupe--clamp (position size view)
  "Clamp POSITION of a window VIEW pixels long over an image SIZE pixels long.
An image smaller than the window is centred, at a negative position."
  (if (<= size view)
      (- (/ (- view size) 2))
    (max 0 (min (round (or position 0)) (- size view)))))

(defun loupe--max-zoom (fit)
  "Return the largest zoom for an image whose fitted size is FIT."
  (max 1.0 (min loupe-max-zoom
                (sqrt (/ loupe-max-pixels
                         (float (max 1 (* (car fit) (cdr fit)))))))))

(defvar-local loupe--exif nil
  "(FILE . DEGREES): the rotation FILE's Exif orientation asks for.")

(defun loupe--exif-rotation (file)
  "Return the rotation that FILE's Exif orientation asks for, in degrees."
  (unless (equal file (car loupe--exif))
    (setq loupe--exif
          (cons file (or (ignore-errors (exif-orientation (exif-parse-file file)))
                         0))))
  (cdr loupe--exif))

(defun loupe--zoomed-spec (base fit zoom rough)
  "Return BASE resized to ZOOM times its FIT size.
ROUGH draws from a proxy without smoothing, for speed during a gesture."
  (let* ((props (copy-sequence (cdr base)))
         (file (plist-get props :file))
         (proxy (and rough file (loupe--proxy file)))
         (rotation (float (mod (- (or (plist-get props :rotation) 0)
                                  (if proxy (loupe--exif-rotation file) 0))
                               360)))
         ;; :width applies before rotation.
         (width (max 1 (round (* zoom (if (= 90 (mod (round rotation) 180))
                                         (cdr fit)
                                       (car fit)))))))
    (dolist (key '(:max-width :max-height :width :height :scale :rotation
                              :transform-smoothing))
      (cl-remf props key))
    (if proxy
        (create-image proxy nil nil :scale 1 :width width :rotation rotation
                      :transform-smoothing nil)
      `(image :scale 1 :width ,width :rotation ,rotation
              :transform-smoothing ,(not rough) ,@props))))

(defun loupe--spec (base fit rough)
  "Return the spec to draw BASE at the current zoom, given its FIT size.
ROUGH draws from a proxy without smoothing.  Drop the zoomed image it
replaces from the image cache."
  (if (= loupe--zoom 1.0)
      (progn (loupe--forget) base)
    (let ((key (list loupe--zoom rough fit)))
      (if (equal key (car loupe--shown))
          (cdr loupe--shown)
        (let ((spec (loupe--zoomed-spec base fit loupe--zoom rough)))
          (loupe--forget)
          (setq loupe--shown (cons key spec))
          spec)))))

(defun loupe--forget ()
  "Drop the zoomed image from the image cache."
  (when loupe--shown
    (image-flush (cdr loupe--shown) t)
    (setq loupe--shown nil)))

(defun loupe-redraw (&optional window rough)
  "Draw this buffer's image in WINDOW at its zoom and position.
ROUGH draws quickly from a proxy while a gesture is under way."
  (let ((window (or window (loupe--window)))
        (base (loupe--base)))
    (if (not (and loupe-image-mode base window
                  (display-graphic-p (window-frame window))))
        (when (overlayp loupe--overlay)
          (delete-overlay loupe--overlay))
      (let* ((frame (window-frame window))
             (fit (image-display-size base t frame))
             (spec (loupe--spec base fit rough))
             (size (image-size spec t frame))
             (box (loupe--box window))
             (iw (round (car size)))
             (ih (round (cdr size)))
             (ww (car box))
             (wh (cdr box))
             (x (loupe--clamp (car loupe--origin) iw ww))
             (y (loupe--clamp (cdr loupe--origin) ih wh))
             (shown-x (- x loupe--shift))
             (x0 (max 0 shown-x))
             (y0 (max 0 y))
             (slice (list 'slice x0 y0
                          (max 1 (- (min iw (+ shown-x ww)) x0))
                          (max 1 (- (min ih (+ y wh)) y0))))
             (overlay (or (and (overlayp loupe--overlay)
                               (overlay-buffer loupe--overlay)
                               loupe--overlay)
                          (setq loupe--overlay
                                (make-overlay (point-min) (point-max))))))
        (when loupe--origin
          (setq loupe--origin (cons x y)))
        (setq loupe--geometry (list shown-x y iw ih))
        (move-overlay overlay (point-min) (point-max))
        (overlay-put overlay 'window window)
        ;; Default image ascent is 50%, so a stretch as tall as the window
        ;; with the same ascent centres the image vertically.
        (overlay-put overlay 'before-string
                     (propertize " " 'display
                                 `(space :width (,(max 0 (- shown-x)))
                                         :height (,wh) :ascent 50)
                                 'pointer 'arrow))
        (overlay-put overlay 'display (list slice spec))
        ;; Not the text I-beam: nothing here takes typing.
        (overlay-put overlay 'pointer 'arrow)
        (set-window-start window (point-min) t)
        (set-window-hscroll window 0)
        (set-window-vscroll window 0 t)))))

(defun loupe--anchor (point)
  "Return the image fraction (U . V) under window POINT (X . Y)."
  (pcase-let ((`(,x ,y ,iw ,ih) (or loupe--geometry '(0 0 1 1))))
    (cons (/ (+ x (car point)) (float (max 1 iw)))
          (/ (+ y (cdr point)) (float (max 1 ih))))))

(defun loupe--zoom-around (zoom anchor point &optional rough window)
  "Set ZOOM so image fraction ANCHOR (U . V) stays at window POINT (X . Y).
Draw in WINDOW, ROUGH unless input is waiting.  Return the zoom used."
  (when-let* ((base (loupe--base))
              (window (or window (loupe--window))))
    (let* ((fit (image-display-size base t (window-frame window)))
           (zoom (max (if rough 0.85 1.0)
                      (min (loupe--max-zoom fit) zoom))))
      (setq loupe--zoom (if (< (abs (- zoom 1.0)) 0.01) 1.0 zoom)
            loupe--origin
            (cons (- (* (car anchor) (car fit) zoom) (car point))
                  (- (* (cdr anchor) (cdr fit) zoom) (cdr point))))
      (unless (and rough (input-pending-p))
        (loupe-redraw window rough))
      loupe--zoom)))

(defun loupe--centre (window)
  "Return the centre of WINDOW's text area as (X . Y)."
  (let ((box (loupe--box window)))
    (cons (/ (car box) 2) (/ (cdr box) 2))))

(defun loupe-zoom-by (factor &optional point rough)
  "Multiply the zoom by FACTOR around window POINT, by default the centre.
ROUGH draws quickly from a proxy, for a gesture still under way."
  (let* ((window (loupe--window))
         (point (or point (loupe--centre window))))
    (loupe--zoom-around (* loupe--zoom factor)
                                 (loupe--anchor point) point rough window)))

(defun loupe--settle (&optional window)
  "Draw the image in WINDOW sharply after a gesture.
Return to fit if the gesture shrank it below that."
  (when (< loupe--zoom 1.0)
    (setq loupe--zoom 1.0
          loupe--origin nil))
  (loupe-redraw window))

(defun loupe--reset (&rest _)
  "Show the image fitted and centred again."
  (when loupe-image-mode
    (setq loupe--zoom 1.0
          loupe--origin nil
          loupe--shift 0)
    (loupe--forget)
    (loupe-redraw)))

(defun loupe--refresh (window)
  "Redraw the image in WINDOW after its size or buffer changed."
  (with-current-buffer (window-buffer window)
    (when loupe-image-mode
      (loupe-redraw window))))

(defun loupe--cleanup ()
  "Remove the zoom overlay and drop the zoomed image."
  (loupe--forget)
  (when (overlayp loupe--overlay)
    (delete-overlay loupe--overlay))
  (setq loupe--overlay nil))

;;;; Proxies

(defvar loupe--worker nil
  "Shell that runs proxy and thumbnail jobs in the background.")

(defun loupe-run-shell (command)
  "Run shell COMMAND in the background and forget it.
Starting a process takes about 0.35 s on the Android APK, which also never
notices one exit, so one long-lived shell runs every job.  Callers watch
for the files COMMAND writes instead of waiting for it."
  (let ((line (format "( %s ) >/dev/null 2>&1 &\n" command)))
    (unless (and (processp loupe--worker)
                 (ignore-errors
                   (process-send-string loupe--worker line)
                   t))
      (setq loupe--worker
            (make-process :name "loupe-worker" :noquery t :connection-type 'pipe
                          :command (list (or (executable-find "sh") shell-file-name))))
      (process-send-string loupe--worker line))))

(defvar loupe--proxy-job nil
  "(PROXY . START) of the proxy being made, or nil.")

(defun loupe--proxy-name (file)
  "Return the cache file for FILE's proxy."
  (let ((attributes (file-attributes file)))
    (expand-file-name
     (concat (md5 (format "%s %s %s" file
                          (file-attribute-size attributes)
                          (file-attribute-modification-time attributes)))
             ".jpg")
     loupe-proxy-directory)))

(defun loupe--proxy (file)
  "Return a proxy of image FILE, or start making one and return nil.
Small files, animations, vector images, and remote files get none."
  (when (and (not (file-remote-p file))
             (string-match-p "\\.\\(?:jpe?g\\|png\\|webp\\|tiff?\\|bmp\\)\\'"
                             (downcase file))
             (> (or (file-attribute-size (file-attributes file)) 0)
                loupe-proxy-min-bytes))
    (let ((proxy (loupe--proxy-name file)))
      (if (file-exists-p proxy)
          proxy
        (loupe--make-proxy file proxy)
        nil))))

(defun loupe--make-proxy (file proxy)
  "Start writing FILE's PROXY in the background, one at a time."
  (when (and loupe--proxy-job
             (or (file-exists-p (car loupe--proxy-job))
                 (> (- (float-time) (cdr loupe--proxy-job)) 30)))
    (setq loupe--proxy-job nil))
  (when-let* (((not loupe--proxy-job))
              (program (or (executable-find "magick")
                           (executable-find "convert"))))
    (let ((partial (concat proxy ".part"))
          (size loupe-proxy-size))
      (make-directory (file-name-directory proxy) t)
      (loupe--prune-proxies)
      (setq loupe--proxy-job (cons proxy (float-time)))
      (loupe-run-shell
       (format "%s && mv -f %s %s"
               (mapconcat #'shell-quote-argument
                          (list program
                                "-define" (format "jpeg:size=%dx%d" (* 2 size) (* 2 size))
                                (concat file "[0]")
                                "-auto-orient"
                                "-thumbnail" (format "%dx%d>" size size)
                                "-quality" "85"
                                (concat "jpeg:" partial))
                          " ")
               (shell-quote-argument partial)
               (shell-quote-argument proxy))))))

(defun loupe--prune-proxies ()
  "Delete the oldest proxies beyond `loupe-proxy-limit'."
  (let* ((directory loupe-proxy-directory)
         (files (and (file-directory-p directory)
                     (directory-files-and-attributes directory t "\\.jpg\\(?:\\.part\\)?\\'" t))))
    (when (> (length files) loupe-proxy-limit)
      (dolist (entry (nthcdr loupe-proxy-limit
                             (sort files
                                   (lambda (a b)
                                     (time-less-p
                                      (file-attribute-modification-time (cdr b))
                                      (file-attribute-modification-time (cdr a)))))))
        (ignore-errors (delete-file (car entry)))))))

;;;; Paging

(defun loupe-next-file (n)
  "Visit the Nth next image, in gallery order or cyclic directory order."
  (interactive "p")
  (if loupe-step-function
      (funcall loupe-step-function n)
    (let ((dired-movement-style 'cycle-files))
      (image-next-file n))))

(defun loupe-previous-file (n)
  "Visit the Nth previous image, in gallery order or cyclic directory order."
  (interactive "p")
  (loupe-next-file (- n)))

(defun loupe-quit ()
  "Leave the image, back to the gallery it came from if any."
  (interactive)
  (if loupe-quit-function
      (funcall loupe-quit-function)
    (quit-window)))

;;;; Keys and mouse

(defun loupe-zoom-in ()
  "Zoom in around the centre of the window."
  (interactive)
  (loupe-zoom-by 1.25))

(defun loupe-zoom-out ()
  "Zoom out around the centre of the window."
  (interactive)
  (loupe-zoom-by 0.8))

(defun loupe--pan (dx dy &optional window)
  "Move the view in WINDOW DX and DY pixels across the zoomed image.
Return non-nil if it moved."
  (let ((before (car loupe--geometry))
        (before-y (cadr loupe--geometry)))
    (pcase-let ((`(,x ,y . ,_) loupe--geometry))
      (setq loupe--origin (cons (+ x dx) (+ y dy))))
    (loupe-redraw window)
    (not (and (equal before (car loupe--geometry))
              (equal before-y (cadr loupe--geometry))))))

(defun loupe--pan-step (dx dy)
  "Pan by fractions DX and DY of the window."
  (let ((box (loupe--box (loupe--window))))
    (loupe--pan (round (* dx (car box))) (round (* dy (cdr box))))))

(defun loupe-left ()
  "Pan left when zoomed, otherwise show the previous image."
  (interactive)
  (if (> loupe--zoom 1.0)
      (loupe--pan-step -0.2 0)
    (loupe-previous-file 1)))

(defun loupe-right ()
  "Pan right when zoomed, otherwise show the next image."
  (interactive)
  (if (> loupe--zoom 1.0)
      (loupe--pan-step 0.2 0)
    (loupe-next-file 1)))

(defun loupe-up ()
  "Pan up when zoomed."
  (interactive)
  (loupe--pan-step 0 -0.2))

(defun loupe-down ()
  "Pan down when zoomed."
  (interactive)
  (loupe--pan-step 0 0.2))

(defun loupe-toggle-zoom (point &optional window)
  "Zoom in on POINT (X . Y) in WINDOW, or back to fit when zoomed."
  (if (> loupe--zoom 1.0)
      (progn (setq loupe--zoom 1.0
                   loupe--origin nil)
             (loupe-redraw window))
    (loupe--zoom-around loupe-double-tap-zoom
                                 (loupe--anchor point) point nil window)))

(defun loupe-mouse-toggle-zoom (event)
  "Zoom in where EVENT clicked, or back to fit when zoomed."
  (interactive "e")
  (let ((posn (event-start event)))
    (with-selected-window (posn-window posn)
      (loupe-toggle-zoom (posn-x-y posn)))))

(defun loupe-mouse-drag (event)
  "Drag a zoomed image with the mouse from EVENT.
A press that does not move hands its click back, so a double click on a
zoomed image still reaches `loupe-mouse-toggle-zoom'."
  (interactive "e")
  (let* ((posn (event-start event))
         (window (posn-window posn))
         (last (posn-x-y posn)))
    (when (and (windowp window)
               (> (buffer-local-value 'loupe--zoom (window-buffer window)) 1.0))
      (with-selected-window window
        (let (next moved)
          (track-mouse
            (while (mouse-movement-p (setq next (read-event)))
              (let ((posn (event-start next)))
                (when (eq (posn-window posn) window)
                  (let ((xy (posn-x-y posn)))
                    (unless (equal xy last)
                      (setq moved t)
                      (loupe--pan (- (car last) (car xy))
                                           (- (cdr last) (cdr xy)) window)
                      (setq last xy)
                      (redisplay)))))))
          (unless moved
            (push next unread-command-events)))))))

(defvar loupe--wheel-flip nil
  "(TOTAL . TIME) of touchpad scrolling toward a flip at fit.
TOTAL is `flipped' once this scroll has flipped.")

(defun loupe--wheel-flip (type delta)
  "Flip to the next or previous image for wheel TYPE at fit.
A mouse flips once per notch.  A touchpad, whose events carry pixel
DELTA, flips once per scroll after 120 pixels."
  (let ((forward (memq type '(wheel-down wheel-right))))
    (if (not (consp delta))
        (loupe-next-file (if forward 1 -1))
      (let* ((now (float-time))
             (state loupe--wheel-flip)
             (total (if (and state (< (- now (cdr state)) 0.3)) (car state) 0)))
        (if (eq total 'flipped)
            (setq loupe--wheel-flip (cons 'flipped now))
          (setq total (+ total (* (if forward 1 -1)
                                  (abs (if (memq type '(wheel-left wheel-right))
                                           (car delta)
                                         (cdr delta))))))
          (if (< (abs total) 120)
              (setq loupe--wheel-flip (cons total now))
            (setq loupe--wheel-flip (cons 'flipped now))
            (loupe-next-file (if (> total 0) 1 -1))))))))

(defun loupe-wheel (event)
  "Pan a zoomed image with wheel EVENT, or flip images at fit.
Control zooms at the pointer."
  (interactive "e")
  (let* ((posn (event-start event))
         (window (posn-window posn))
         (type (event-basic-type event))
         (delta (nth 4 event))
         (clicks (or (nth 2 event) 1)))
    (when (windowp window)
      (with-selected-window window
        (cond
         ((memq 'control (event-modifiers event))
          (loupe-zoom-by (if (eq type 'wheel-up) 1.15 (/ 1 1.15))
                                  (posn-x-y posn) t)
          (loupe--settle-later window))
         ((<= loupe--zoom 1.0)
          (loupe--wheel-flip type delta))
         (t
          (let ((pixels (if (consp delta)
                            (max (abs (car delta)) (abs (cdr delta)))
                          (* 80 clicks))))
            (pcase type
              ('wheel-down (loupe--pan 0 pixels))
              ('wheel-up (loupe--pan 0 (- pixels)))
              ('wheel-right (loupe--pan pixels 0))
              ('wheel-left (loupe--pan (- pixels) 0))))))))))

(defvar loupe--settle-timer nil
  "Timer that draws the image sharply once a gesture pauses.")

(defun loupe--settle-later (window &optional delay)
  "Draw WINDOW's image sharply after DELAY idle seconds."
  (when (timerp loupe--settle-timer)
    (cancel-timer loupe--settle-timer))
  (setq loupe--settle-timer
        (run-with-idle-timer
         (or delay 0.2) nil
         (lambda ()
           (when (window-live-p window)
             (with-current-buffer (window-buffer window)
               (when (derived-mode-p 'image-mode)
                 (loupe--settle window))))))))

(defvar loupe--pinch-start nil
  "(ZOOM ANCHOR X Y) when the current touchpad pinch began.")

(defun loupe-pinch (event)
  "Zoom with touchpad pinch EVENT around the pointer."
  (interactive "e")
  (pcase-let* ((`(,_ ,posn ,dx ,dy ,scale ,angle) event)
               (window (posn-window posn)))
    (when (windowp window)
      (with-selected-window window
        (when (or (null loupe--pinch-start)
                  (and (zerop dx) (zerop dy) (zerop angle)))
          (let ((xy (posn-x-y posn)))
            (setq loupe--pinch-start
                  (list loupe--zoom (loupe--anchor xy)
                        (car xy) (cdr xy)))))
        (pcase-let ((`(,zoom ,anchor ,x ,y) loupe--pinch-start))
          (setf (nth 2 loupe--pinch-start) (+ x dx)
                (nth 3 loupe--pinch-start) (+ y dy))
          (loupe--zoom-around (* zoom scale) anchor
                                       (cons (+ x dx) (+ y dy)) t window))
        (loupe--settle-later window)))))

;;;; Touch

(defvar loupe--touch nil
  "The touch gesture on an image, a plist.
:window is the image's window, :points the fingers as ((ID X . Y) ...),
:mode nil until they move, then `pan', `swipe', `still', or `pinch'.
:start is (X Y TIME) of the first finger, :pinch is (DISTANCE ZOOM
ANCHOR) when the second finger landed, and :trail holds recent (TIME X
. Y) of a moving finger, newest first.")

(defvar loupe--last-tap nil
  "(TIME X . Y) of the last tap on an image, to spot a double tap.")

(defconst loupe--slop 16
  "Pixels a finger moves before a touch stops being a tap.")

(defun loupe--distance (a b)
  "Return the distance between points A and B."
  (max 1.0 (sqrt (+ (expt (- (car a) (car b)) 2)
                    (expt (- (cdr a) (cdr b)) 2)))))

(defun loupe--midpoint (a b)
  "Return the midpoint of A and B."
  (cons (/ (+ (car a) (car b)) 2.0) (/ (+ (cdr a) (cdr b)) 2.0)))

(defun loupe--velocity (trail)
  "Return the (VX . VY) pixels per second of the last 0.1 s of TRAIL."
  (let* ((newest (car trail))
         (oldest (car (last (seq-take-while
                             (lambda (sample) (<= (- (car newest) (car sample)) 100))
                             trail))))
         (dt (and oldest (/ (- (car newest) (car oldest)) 1000.0))))
    (if (and dt (> dt 0))
        (cons (/ (- (cadr newest) (cadr oldest)) dt)
              (/ (- (cddr newest) (cddr oldest)) dt))
      (cons 0 0))))

(defun loupe-touch (event)
  "Zoom, pan, flip, or double-tap an image with touch EVENT."
  (interactive "e")
  (require 'touch-screen)
  (pcase (car event)
    ('touchscreen-begin (loupe--touch-begin (cadr event)))
    ('touchscreen-update (loupe--touch-update (cadr event)))
    ('touchscreen-end (loupe--touch-end (cadr event) (caddr event)))))

(defun loupe--touch-begin (point)
  "Start tracking finger POINT, an (ID . POSN)."
  (let* ((posn (cdr point))
         (window (posn-window posn)))
    (when (windowp window)
      (when (timerp loupe--settle-timer)
        (cancel-timer loupe--settle-timer))
      ;; A second finger joins the gesture; anything else starts a new one,
      ;; even if an earlier finger's end event went missing.
      (unless (and (= 1 (length (plist-get loupe--touch :points)))
                   (eq window (plist-get loupe--touch :window)))
        (select-window window)
        (let ((xy (posn-x-y posn)))
          (setq loupe--touch
                (list :window window :points nil :mode nil
                      :start (list (car xy) (cdr xy) (posn-timestamp posn))))))
      (let* ((touch loupe--touch)
             (points (cons (cons (car point)
                                 (touch-screen-relative-xy
                                  posn (plist-get touch :window)))
                           (plist-get touch :points))))
        (setq loupe--touch (plist-put touch :points points))
        (when (= (length points) 2)
          (let ((a (cdar points))
                (b (cdadr points)))
            (with-selected-window (plist-get touch :window)
              (setq loupe--touch
                    (plist-put (plist-put loupe--touch :mode 'pinch)
                               :pinch (list (loupe--distance a b)
                                            loupe--zoom
                                            (loupe--anchor
                                             (loupe--midpoint a b))))))))))))

(defun loupe--touch-update (moved)
  "Follow MOVED fingers, a list of (ID . POSN)."
  (let* ((touch loupe--touch)
         (window (plist-get touch :window))
         (points (plist-get touch :points))
         delta)
    (when (and (window-live-p window) points)
      (dolist (finger moved)
        (when-let* ((cell (assq (car finger) points)))
          (let ((xy (touch-screen-relative-xy (cdr finger) window)))
            (when (eq cell (car (last points)))
              ;; The first finger down drives a pan or a swipe.
              (setq delta (list (posn-timestamp (cdr finger))
                                (- (car xy) (cadr cell))
                                (- (cdr xy) (cddr cell))
                                xy)))
            (setcdr cell xy))))
      (with-selected-window window
        (if (eq (plist-get touch :mode) 'pinch)
            (when (>= (length points) 2)
              (pcase-let ((`(,distance ,zoom ,anchor) (plist-get touch :pinch))
                          (a (cdar points))
                          (b (cdadr points)))
                (loupe--zoom-around
                 (* zoom (/ (loupe--distance a b) distance))
                 anchor (loupe--midpoint a b) t window)))
          (when delta
            (pcase-let ((`(,time ,dx ,dy ,xy) delta)
                        (`(,x0 ,y0 . ,_) (plist-get touch :start)))
              (let ((mode (plist-get touch :mode))
                    (tx (- (car xy) x0))
                    (ty (- (cdr xy) y0)))
                (unless (or mode (< (max (abs tx) (abs ty)) loupe--slop))
                  (setq mode (cond ((> loupe--zoom 1.0) 'pan)
                                   ((> (abs tx) (abs ty)) 'swipe)
                                   (t 'still))))
                (setq touch (plist-put touch :mode mode))
                (setq touch (plist-put touch :trail
                                       (seq-take (cons (cons time xy)
                                                       (plist-get touch :trail))
                                                 20)))
                (pcase mode
                  ('pan (loupe--pan (- dx) (- dy) window))
                  ('swipe (setq loupe--shift tx)
                          (loupe-redraw window)))
                (setq loupe--touch touch)))))))))

(defun loupe--touch-end (point canceled)
  "Finish finger POINT, an (ID . POSN); CANCELED means the system took it."
  (let* ((touch loupe--touch)
         (window (plist-get touch :window))
         (points (assq-delete-all (car point) (plist-get touch :points)))
         (mode (plist-get touch :mode)))
    (setq loupe--touch (plist-put touch :points points))
    (when (window-live-p window)
      (with-selected-window window
        (cond
         (canceled
          (setq loupe--shift 0)
          (loupe--settle window))
         ((eq mode 'pinch)
          (if points
              ;; Keep panning with the finger still down.
              (setq loupe--touch
                    (plist-put (plist-put loupe--touch :mode 'pan)
                               :trail nil))
            (loupe--settle window)))
         (points nil)
         ((eq mode 'pan)
          (let ((velocity (loupe--velocity (plist-get touch :trail))))
            (loupe--glide window (- (car velocity)) (- (cdr velocity))))
          ;; A pinch that ended one finger at a time is still rough.
          (when (cadr (car loupe--shown))
            (loupe--settle window)))
         ((eq mode 'swipe)
          (loupe--finish-swipe
           window (car (loupe--velocity (plist-get touch :trail)))))
         ((null mode)
          (loupe--tap window (cdr point))))))))

(defun loupe--tap (window posn)
  "Handle a tap at POSN in WINDOW, zooming on a double tap."
  (let ((time (posn-timestamp posn))
        (xy (touch-screen-relative-xy posn window))
        (last loupe--last-tap))
    (if (and last
             (< (- time (car last)) 350)
             (< (loupe--distance xy (cdr last)) 60))
        (progn (setq loupe--last-tap nil)
               (loupe-toggle-zoom xy window))
      (setq loupe--last-tap (cons time xy)))))

(defun loupe--glide (window vx vy)
  "Keep panning WINDOW at VX and VY pixels per second, slowing down.
Any input stops it, as a touch-screen fling does."
  (let ((last (float-time))
        (carry-x 0.0)
        (carry-y 0.0))
    (while (and (> (sqrt (+ (* vx vx) (* vy vy))) 30)
                (sit-for 0.001))
      (let* ((now (float-time))
             (dt (- now last))
             (decay (exp (- (/ dt 0.35))))
             (tx (+ carry-x (* vx dt)))
             (ty (+ carry-y (* vy dt)))
             (px (truncate tx))
             (py (truncate ty)))
        (setq last now
              carry-x (- tx px)
              carry-y (- ty py)
              vx (* vx decay)
              vy (* vy decay))
        (unless (and (zerop px) (zerop py))
          (unless (loupe--pan px py window)
            (setq vx 0 vy 0)))))))

(defun loupe--slide (window target)
  "Slide the fitted image in WINDOW sideways to TARGET pixels."
  (let ((start loupe--shift)
        (began (float-time)))
    (while (and (/= loupe--shift target)
                (sit-for 0.001))
      (let ((progress (min 1.0 (/ (- (float-time) began) 0.15))))
        (setq loupe--shift
              (round (+ start (* progress (- target start)))))
        (loupe-redraw window)))))

(defun loupe--finish-swipe (window velocity)
  "Flip WINDOW to the next or previous image, or slide back, after a swipe.
VELOCITY is the finger's sideways speed when it lifted."
  (let* ((width (car (loupe--box window)))
         (shift loupe--shift)
         (flip (or (> (abs shift) (* 0.25 width))
                   (and (> (abs shift) 40) (> (abs velocity) 800)
                        (eq (> shift 0) (> velocity 0))))))
    (if (not flip)
        (loupe--slide window 0)
      (loupe--slide window (if (> shift 0) width (- width)))
      (setq loupe--shift 0)
      (condition-case err
          (if (> shift 0)
              (loupe-previous-file 1)
            (loupe-next-file 1))
        (error (loupe-redraw window)
               (message "%s" (error-message-string err)))))))

;;;; Image mode

(defun loupe-rotate (&optional degrees)
  "Rotate the image DEGREES clockwise, by default 90."
  (interactive)
  (image-transform-set-rotation (+ image-transform-rotation (or degrees 90))))

(defun loupe-rotate-counterclockwise ()
  "Rotate the image 90 degrees counterclockwise."
  (interactive)
  (loupe-rotate -90))

(defun loupe--own-display (get)
  "Return Image mode's own image from GET, not the zoom overlay's slice."
  (or (and loupe-image-mode (loupe--base))
      (funcall get)))

;;;; Modes

(defun loupe--image-setup ()
  "Prepare an Image mode buffer for zooming, panning, and paging."
  (when (and loupe-mode (derived-mode-p 'image-mode))
    (loupe-image-mode 1)))

;; DocView's map inherits Image mode's, so gestures live in a minor mode
;; that only real image buffers enable.
(defvar-keymap loupe-image-mode-map
  :doc "Zoom, pan, and paging keys in Image mode."
  "q" #'loupe-quit
  "n" #'loupe-next-file
  "p" #'loupe-previous-file
  "r" #'loupe-rotate
  "R" #'loupe-rotate-counterclockwise
  "0" #'image-transform-reset-to-initial
  "G" #'loupe-gallery
  "=" #'loupe-zoom-in
  "+" #'loupe-zoom-in
  "-" #'loupe-zoom-out
  "<left>" #'loupe-left
  "<right>" #'loupe-right
  "<up>" #'loupe-up
  "<down>" #'loupe-down
  "<down-mouse-1>" #'loupe-mouse-drag
  "<double-mouse-1>" #'loupe-mouse-toggle-zoom
  "<wheel-up>" #'loupe-wheel
  "<wheel-down>" #'loupe-wheel
  "<wheel-left>" #'loupe-wheel
  "<wheel-right>" #'loupe-wheel
  "C-<wheel-up>" #'loupe-wheel
  "C-<wheel-down>" #'loupe-wheel
  "<pinch>" #'loupe-pinch
  ;; Raw touch events bypass touch-screen.el's scrolling and text-scale
  ;; pinch, so gestures reach the image directly.
  "<touchscreen-begin>" #'loupe-touch
  "<touchscreen-update>" #'loupe-touch
  "<touchscreen-end>" #'loupe-touch)

(define-minor-mode loupe-image-mode
  "Zoom, pan, and flip through images by touch, touchpad, mouse, and keys."
  :keymap loupe-image-mode-map
  (if loupe-image-mode
      (progn
        (goto-char (point-min))
        (setq-local cursor-type nil
                    ;; The drawn row ends at the window edge.
                    fringe-indicator-alist
                    (cons '(truncation nil nil) fringe-indicator-alist))
        (add-hook 'window-buffer-change-functions #'loupe--refresh nil t)
        (add-hook 'window-size-change-functions #'loupe--refresh nil t)
        (add-hook 'change-major-mode-hook #'loupe--cleanup nil t)
        (add-hook 'kill-buffer-hook #'loupe--cleanup nil t)
        (when (and buffer-file-name (display-graphic-p))
          (loupe--proxy buffer-file-name))
        (loupe-redraw))
    (remove-hook 'window-buffer-change-functions #'loupe--refresh t)
    (remove-hook 'window-size-change-functions #'loupe--refresh t)
    (remove-hook 'change-major-mode-hook #'loupe--cleanup t)
    (remove-hook 'kill-buffer-hook #'loupe--cleanup t)
    (kill-local-variable 'cursor-type)
    (kill-local-variable 'fringe-indicator-alist)
    (loupe--cleanup)))

;;;; Documents

;; DocView and PDF Tools show one page image at a time, scrolled with the
;; window's vscroll and hscroll.  Touch drives those directly, as
;; touch-screen.el's line-based scrolling cannot move through a single tall
;; image.  A zoom first draws the page roughly at the new size, then once
;; the gesture ends asks the viewer to render it.

(defvar loupe--document-touch nil
  "The touch gesture on a document page, a plist like `loupe--touch'.
:pinch is (DISTANCE WIDTH ANCHOR SPEC) when the second finger landed.")

(defvar loupe--document-live nil
  "Rough page spec drawn during a zoom gesture, or nil.")

(defun loupe--document-page ()
  "Return the page number shown in the selected window."
  (image-mode-window-get 'page))

(defun loupe--document-pages ()
  "Return the number of pages in the document."
  (if (derived-mode-p 'pdf-view-mode)
      (pdf-cache-number-of-pages)
    (doc-view-last-page-number)))

(defun loupe--document-turn (n)
  "Show the page N pages on."
  (if (derived-mode-p 'pdf-view-mode)
      (pdf-view-next-page n)
    (doc-view-next-page n)))

(defun loupe--document-geometry ()
  "Return (WIDTH HEIGHT WINDOW-WIDTH WINDOW-HEIGHT LEFT) of the shown page.
LEFT is the page's offset when it is narrower than the window."
  (when-let* ((image (overlay-get (image-mode-window-get 'overlay) 'display))
              ((eq (car-safe image) 'image)))
    (let ((size (image-size image t))
          (box (loupe--box (selected-window))))
      (list (round (car size)) (round (cdr size)) (car box) (cdr box)
            (max 0 (/ (- (car box) (round (car size))) 2))))))

(defun loupe--document-anchor (point)
  "Return the page fraction (U . V) under window POINT (X . Y)."
  (pcase-let ((`(,iw ,ih ,_ ,_ ,left) (loupe--document-geometry)))
    (cons (/ (+ (car point) (- left) (* (window-hscroll) (frame-char-width)))
             (float (max 1 iw)))
          (/ (+ (cdr point) (window-vscroll nil t)) (float (max 1 ih))))))

(defun loupe--document-scroll-to (anchor point)
  "Scroll so page fraction ANCHOR (U . V) sits at window POINT (X . Y)."
  (pcase-let ((`(,iw ,ih ,ww ,wh ,left) (loupe--document-geometry)))
    (image-set-window-vscroll
     (max 0 (min (max 0 (- ih wh)) (round (- (* (cdr anchor) ih) (cdr point))))))
    (image-set-window-hscroll
     (if (<= iw ww)
         0
       (max 0 (min (ceiling (- iw ww) (frame-char-width))
                   (round (- (+ (* (car anchor) iw) left) (car point))
                          (frame-char-width))))))))

(defun loupe--document-edges ()
  "Return which edges of the page show: (TOP . BOTTOM)."
  (pcase-let ((`(,_ ,ih ,_ ,wh ,_) (loupe--document-geometry)))
    (cons (<= (window-vscroll nil t) 0)
          (>= (window-vscroll nil t) (max 0 (- (or ih 0) (or wh 0)))))))

(defun loupe--document-pan (dx dy &optional turn)
  "Scroll the page DX and DY pixels; return non-nil if anything moved.
With TURN, a drag that began at an edge of the page and goes a quarter of
the window past it turns the page."
  (pcase-let* ((`(,iw ,ih ,ww ,wh ,_) (loupe--document-geometry))
               (vscroll (window-vscroll nil t))
               (target (+ vscroll dy))
               (limit (max 0 (- ih wh)))
               (page (loupe--document-page))
               (hscroll (window-hscroll))
               (edges (plist-get loupe--document-touch :edges))
               (moved nil))
    (image-set-window-vscroll (max 0 (min limit target)))
    (setq moved (/= vscroll (window-vscroll nil t)))
    (when turn
      (let ((over (+ (or (plist-get loupe--document-touch :overscroll) 0)
                     (cond ((and (> target limit) (cdr edges)) (- target limit))
                           ((and (< target 0) (car edges)) target)
                           (t 0))))
            (half (* 0.25 wh)))
        (cond
         ((and (>= over half) (< page (loupe--document-pages)))
          (loupe--document-turn 1)
          (image-set-window-vscroll 0)
          (setq over 0 edges nil moved 'turned))
         ((and (<= over (- half)) (> page 1))
          (loupe--document-turn -1)
          (pcase-let ((`(,_ ,ih ,_ ,wh ,_) (loupe--document-geometry)))
            (image-set-window-vscroll (max 0 (- ih wh))))
          (setq over 0 edges nil moved 'turned)))
        (setq loupe--document-touch
              (plist-put (plist-put loupe--document-touch :overscroll over)
                         :edges edges))
        ;; A turn ends the drag, so the new page shows from its edge.
        (when (eq moved 'turned)
          (setq loupe--document-touch
                (plist-put loupe--document-touch :mode 'turned)))))
    (when (> iw ww)
      (let* ((pixels (+ (plist-get loupe--document-touch :hpixels) dx))
             (columns (truncate pixels (frame-char-width))))
        (setq loupe--document-touch
              (plist-put loupe--document-touch :hpixels
                         (- pixels (* columns (frame-char-width)))))
        (image-set-window-hscroll
         (max 0 (min (ceiling (- iw ww) (frame-char-width)) (+ hscroll columns))))
        (setq moved (or moved (/= hscroll (window-hscroll))))))
    moved))

(defun loupe--document-clamp (factor width)
  "Limit FACTOR so a page WIDTH pixels wide stays within 0.5 to 4 windows."
  (let ((window-width (car (loupe--box (selected-window)))))
    (max (/ (* 0.5 window-width) width)
         (min (/ (* 4.0 window-width) width) factor))))

(defun loupe--document-resize (factor anchor point)
  "Render the page FACTOR times larger, keeping fraction ANCHOR at POINT."
  (let ((factor (loupe--document-clamp
                 factor (max 1 (car (loupe--document-geometry))))))
    (cond ((> (abs (- factor 1.0)) 0.02)
           (if (derived-mode-p 'pdf-view-mode)
               (pdf-view-enlarge factor)
             (doc-view-enlarge factor)))
          ((derived-mode-p 'pdf-view-mode) (pdf-view-redisplay))
          (t (doc-view-goto-page (loupe--document-page))))
    (loupe--document-scroll-to anchor point)))

(defun loupe--document-forget-live ()
  "Drop the rough page drawn during a zoom from the image cache."
  (when loupe--document-live
    (image-flush loupe--document-live t)
    (setq loupe--document-live nil)))

(defun loupe--document-draw-live (spec width ratio anchor point)
  "Draw page SPEC, WIDTH pixels wide as drawn, roughly RATIO times larger.
Keep page fraction ANCHOR at window POINT."
  (let ((props (copy-sequence (cdr spec))))
    (dolist (key '(:width :height :max-width :max-height :scale
                          :transform-smoothing))
      (cl-remf props key))
    (let* ((window-width (car (loupe--box (selected-window))))
           (new (max 1 (round (* width (loupe--document-clamp ratio width)))))
           (live `(image :width ,new :scale 1 :transform-smoothing nil ,@props))
           (overlay (image-mode-window-get 'overlay)))
      (loupe--document-forget-live)
      (setq loupe--document-live live)
      (overlay-put overlay 'display live)
      (overlay-put overlay 'before-string
                   (when (> window-width new)
                     (propertize " " 'display
                                 `(space :align-to (+ center (-0.5 . (,new)))))))
      (loupe--document-scroll-to anchor point))))

(defun loupe--document-settle (spec width anchor point)
  "Render the page sharply at the live zoom of SPEC, drawn WIDTH pixels wide.
Keep page fraction ANCHOR at window POINT.  Put SPEC back first: PDF Tools
measures the page from what is drawn."
  (when-let* ((live loupe--document-live))
    (let ((new (plist-get (cdr live) :width)))
      (loupe--document-forget-live)
      (overlay-put (image-mode-window-get 'overlay) 'display spec)
      (loupe--document-resize (/ new (float width)) anchor point))))

;;;;; Touchpad and wheel

(defvar loupe--document-pinch nil
  "(WINDOW ANCHOR POINT SPEC WIDTH) of the touchpad pinch under way.")

(defvar loupe--document-pinch-timer nil
  "Timer that renders the page sharply once a touchpad pinch pauses.")

(defun loupe-document-pinch (event)
  "Zoom the page around the pointer with touchpad pinch EVENT."
  (interactive "e")
  (pcase-let* ((`(,_ ,posn ,dx ,dy ,scale ,angle) event)
               (window (posn-window posn)))
    (when (windowp window)
      (with-selected-window window
        (when (or (not (eq (car loupe--document-pinch) window))
                  (and (zerop dx) (zerop dy) (zerop angle)))
          (setq loupe--document-pinch
                (when-let* ((spec (overlay-get (image-mode-window-get 'overlay)
                                               'display))
                            ((eq (car-safe spec) 'image))
                            (point (posn-x-y posn)))
                  (list window (loupe--document-anchor point) point spec
                        (car (loupe--document-geometry))))))
        (pcase-let ((`(,_ ,anchor ,point ,spec ,width) loupe--document-pinch))
          (when spec
            (unless (input-pending-p)
              (loupe--document-draw-live spec width scale anchor point))
            (when (timerp loupe--document-pinch-timer)
              (cancel-timer loupe--document-pinch-timer))
            (setq loupe--document-pinch-timer
                  (run-with-idle-timer
                   0.25 nil
                   (lambda ()
                     (when (window-live-p window)
                       (with-selected-window window
                         (setq loupe--document-pinch nil)
                         (loupe--document-settle spec width anchor point))))))))))))

(defun loupe-document-wheel-zoom (event)
  "Zoom the page around the pointer by one step of Control-wheel EVENT."
  (interactive "e")
  (let* ((posn (event-start event))
         (window (posn-window posn)))
    (when (windowp window)
      (with-selected-window window
        (let ((point (posn-x-y posn)))
          (loupe--document-resize
           (if (eq (event-basic-type event) 'wheel-up) 1.15 (/ 1 1.15))
           (loupe--document-anchor point) point))))))

(defun loupe-document-touch (event)
  "Scroll, zoom, or double-tap a document page with touch EVENT."
  (interactive "e")
  (require 'touch-screen)
  (pcase (car event)
    ('touchscreen-begin (loupe--document-touch-begin (cadr event)))
    ('touchscreen-update (loupe--document-touch-update (cadr event)))
    ('touchscreen-end (loupe--document-touch-end (cadr event) (caddr event)))))

(defun loupe--document-touch-begin (point)
  "Start tracking finger POINT, an (ID . POSN)."
  (let* ((posn (cdr point))
         (window (posn-window posn)))
    (when (windowp window)
      (unless (and (= 1 (length (plist-get loupe--document-touch :points)))
                   (eq window (plist-get loupe--document-touch :window)))
        (select-window window)
        (let ((xy (posn-x-y posn)))
          (setq loupe--document-touch
                (list :window window :points nil :mode nil :hpixels 0
                      :edges (with-selected-window window
                               (loupe--document-edges))
                      :start (list (car xy) (cdr xy) (posn-timestamp posn))))))
      (let ((points (cons (cons (car point) (touch-screen-relative-xy posn window))
                          (plist-get loupe--document-touch :points))))
        (setq loupe--document-touch
              (plist-put loupe--document-touch :points points))
        (when (= (length points) 2)
          (with-selected-window window
            (when-let* ((geometry (loupe--document-geometry))
                        (spec (overlay-get (image-mode-window-get 'overlay) 'display)))
              (let ((middle (loupe--midpoint (cdar points) (cdadr points))))
                (setq loupe--document-touch
                      (plist-put (plist-put loupe--document-touch :mode 'pinch)
                                 :pinch (list (loupe--distance
                                               (cdar points) (cdadr points))
                                              (car geometry)
                                              (loupe--document-anchor middle)
                                              spec)))))))))))

(defun loupe--document-touch-update (moved)
  "Follow MOVED fingers, a list of (ID . POSN)."
  (let* ((touch loupe--document-touch)
         (window (plist-get touch :window))
         (points (plist-get touch :points))
         delta)
    (when (and (window-live-p window) points)
      (dolist (finger moved)
        (when-let* ((cell (assq (car finger) points)))
          (let ((xy (touch-screen-relative-xy (cdr finger) window)))
            (when (eq cell (car (last points)))
              (setq delta (list (posn-timestamp (cdr finger))
                                (- (car xy) (cadr cell))
                                (- (cdr xy) (cddr cell))
                                xy)))
            (setcdr cell xy))))
      (with-selected-window window
        (if (eq (plist-get touch :mode) 'pinch)
            (when (and (>= (length points) 2) (plist-get touch :pinch)
                       (not (input-pending-p)))
              (let ((a (cdar points)) (b (cdadr points)))
                (pcase-let ((`(,distance ,width ,anchor ,spec) (plist-get touch :pinch)))
                  (loupe--document-draw-live
                   spec width (/ (loupe--distance a b) distance)
                   anchor (loupe--midpoint a b)))))
          (when delta
            (pcase-let ((`(,time ,dx ,dy ,xy) delta)
                        (`(,x0 ,y0 . ,_) (plist-get touch :start)))
              (let ((mode (plist-get touch :mode)))
                (unless (or mode (< (max (abs (- (car xy) x0)) (abs (- (cdr xy) y0)))
                                    loupe--slop))
                  (setq mode 'pan))
                (setq touch (plist-put touch :mode mode))
                (setq touch (plist-put touch :trail
                                       (seq-take (cons (cons time xy)
                                                       (plist-get touch :trail))
                                                 20)))
                (setq loupe--document-touch touch)
                (when (eq mode 'pan)
                  (loupe--document-pan (- dx) (- dy) t))))))))))

(defun loupe--document-touch-end (point canceled)
  "Finish finger POINT, an (ID . POSN); CANCELED means the system took it."
  (let* ((touch loupe--document-touch)
         (window (plist-get touch :window))
         (points (assq-delete-all (car point) (plist-get touch :points)))
         (mode (plist-get touch :mode)))
    (setq loupe--document-touch (plist-put touch :points points))
    (when (window-live-p window)
      (with-selected-window window
        (cond
         ((eq mode 'pinch)
          (when-let* ((pinch (plist-get touch :pinch)))
            ;; Render sharply at the size the fingers chose, once.
            (let* ((middle (if points
                               (cdar points)
                             (touch-screen-relative-xy (cdr point) window))))
              (setq loupe--document-touch
                    (plist-put loupe--document-touch :pinch nil))
              (loupe--document-settle (nth 3 pinch) (nth 1 pinch)
                                         (loupe--document-anchor middle)
                                         middle)))
          (setq loupe--document-touch
                (plist-put (plist-put loupe--document-touch :mode (and points 'pan))
                           :trail nil)))
         ((or points canceled) nil)
         ((eq mode 'pan)
          (let ((velocity (loupe--velocity (plist-get touch :trail))))
            (loupe--document-glide (- (car velocity)) (- (cdr velocity)))))
         ((null mode)
          (loupe--document-tap (cdr point) window)))))))

(defun loupe--document-glide (vx vy)
  "Keep scrolling at VX and VY pixels per second, slowing down."
  (let ((last (float-time))
        (carry-x 0.0)
        (carry-y 0.0))
    (while (and (> (sqrt (+ (* vx vx) (* vy vy))) 30)
                (sit-for 0.001))
      (let* ((now (float-time))
             (dt (- now last))
             (decay (exp (- (/ dt 0.35))))
             (tx (+ carry-x (* vx dt)))
             (ty (+ carry-y (* vy dt)))
             (px (truncate tx))
             (py (truncate ty)))
        (setq last now
              carry-x (- tx px)
              carry-y (- ty py)
              vx (* vx decay)
              vy (* vy decay))
        (unless (and (zerop px) (zerop py))
          (unless (loupe--document-pan px py)
            (setq vx 0 vy 0)))))))

(defun loupe--document-tap (posn window)
  "Zoom in on a double tap at POSN in WINDOW, or back to the window width."
  (let ((time (posn-timestamp posn))
        (xy (touch-screen-relative-xy posn window))
        (last loupe--last-tap))
    (if (not (and last
                  (< (- time (car last)) 350)
                  (< (loupe--distance xy (cdr last)) 60)))
        (setq loupe--last-tap (cons time xy))
      (setq loupe--last-tap nil)
      (when-let* ((geometry (loupe--document-geometry)))
        (let ((anchor (loupe--document-anchor xy))
              (width (car geometry))
              (window-width (nth 2 geometry)))
          (loupe--document-resize
           (if (> width (* 1.05 window-width))
               (/ window-width (float width))
             2.0)
           anchor xy))))))

(defvar-keymap loupe-document-mode-map
  :doc "Touch, touchpad, and Control-wheel zoom on document pages."
  "<touchscreen-begin>" #'loupe-document-touch
  "<touchscreen-update>" #'loupe-document-touch
  "<touchscreen-end>" #'loupe-document-touch
  "<pinch>" #'loupe-document-pinch
  "C-<wheel-up>" #'loupe-document-wheel-zoom
  "C-<wheel-down>" #'loupe-document-wheel-zoom)

(define-minor-mode loupe-document-mode
  "Scroll, zoom, and double-tap DocView and PDF Tools pages."
  :keymap loupe-document-mode-map
  (when (and loupe-document-mode (derived-mode-p 'doc-view-mode))
    ;; DocView passes no :scale, so a high-density screen would multiply
    ;; every page by `image-scaling-factor' (about 2.8 on a phone).
    (setq-local image-scaling-factor 1.0)
    (when loupe-document-fit-width
      (setq-local doc-view-image-width
                  (window-body-width (or (get-buffer-window) (selected-window))
                                     t)))))

(defun loupe--document-setup ()
  "Take gestures in a DocView or PDF Tools buffer."
  (when loupe-mode
    (loupe-document-mode 1)))

;;;###autoload
(define-minor-mode loupe-mode
  "Pinch, pan, and swipe images and PDFs.
Enables `loupe-image-mode' in Image mode buffers and
`loupe-document-mode' in DocView and PDF Tools buffers."
  :global t
  :group 'loupe
  (if loupe-mode
      (progn
        (add-hook 'image-mode-hook #'loupe--image-setup)
        (add-hook 'doc-view-mode-hook #'loupe--document-setup)
        (add-hook 'pdf-view-mode-hook #'loupe--document-setup)
        ;; Image mode rebuilds its image after a revert, rotation, or refit.
        (advice-add 'image-toggle-display-image :after #'loupe--reset)
        (advice-add 'image-toggle-display-text :after #'loupe--reset)
        (advice-add 'image-get-display-property :around #'loupe--own-display))
    (remove-hook 'image-mode-hook #'loupe--image-setup)
    (remove-hook 'doc-view-mode-hook #'loupe--document-setup)
    (remove-hook 'pdf-view-mode-hook #'loupe--document-setup)
    (advice-remove 'image-toggle-display-image #'loupe--reset)
    (advice-remove 'image-toggle-display-text #'loupe--reset)
    (advice-remove 'image-get-display-property #'loupe--own-display))
  (dolist (buffer (buffer-list))
    (with-current-buffer buffer
      (cond ((derived-mode-p 'image-mode)
             (loupe-image-mode (if loupe-mode 1 -1)))
            ((derived-mode-p 'doc-view-mode 'pdf-view-mode)
             (loupe-document-mode (if loupe-mode 1 -1)))))))

(provide 'loupe)
;;; loupe.el ends here
