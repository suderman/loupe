;;; loupe-test.el --- Checks for loupe -*- lexical-binding: t; -*-

;;; Commentary:
;; Runs in batch Emacs without a display or personal configuration.

;;; Code:

(require 'cl-lib)
(require 'ert)
(require 'loupe)
(require 'loupe-gallery)

;;;; Geometry

(ert-deftest loupe-clamp-centres-small-images-and-bounds-large-ones ()
  (should (= (loupe--clamp 100 400 1000) -300))
  (should (= (loupe--clamp -50 2000 1000) 0))
  (should (= (loupe--clamp 5000 2000 1000) 1000))
  (should (= (loupe--clamp 412.6 2000 1000) 413)))

(ert-deftest loupe-max-zoom-respects-the-pixel-budget ()
  (let ((loupe-max-zoom 8.0)
        (loupe-max-pixels 24000000))
    (should (= (loupe--max-zoom '(16 . 16)) 8.0))
    (should (< (abs (- (loupe--max-zoom '(1000 . 1500)) 4.0)) 0.001))
    (should (= (loupe--max-zoom '(8000 . 8000)) 1.0))))

(ert-deftest loupe-anchor-is-the-image-fraction-under-a-point ()
  (with-temp-buffer
    (setq loupe--geometry '(-100 0 800 600))
    (should (equal (loupe--anchor '(500 . 300)) '(0.5 . 0.5)))
    (setq loupe--geometry '(400 200 2000 1500))
    (should (equal (loupe--anchor '(600 . 550)) '(0.5 . 0.5)))))

(ert-deftest loupe-velocity-uses-the-last-tenth-of-a-second ()
  ;; Newest first: (TIME X . Y), times in milliseconds.
  (let ((trail '((1100 300 . 0) (1050 200 . 0) (1000 100 . 0) (500 0 . 0))))
    (should (equal (loupe--velocity trail) '(2000.0 . 0.0))))
  (should (equal (loupe--velocity '((1000 10 . 10))) '(0 . 0))))

(ert-deftest loupe-distance-and-midpoint ()
  (should (= (loupe--distance '(0 . 0) '(3 . 4)) 5.0))
  (should (= (loupe--distance '(1 . 1) '(1 . 1)) 1.0))
  (should (equal (loupe--midpoint '(0 . 0) '(10 . 20)) '(5.0 . 10.0))))

;;;; Proxies and thumbnails

(ert-deftest loupe-proxy-names-follow-file-size-and-time ()
  (let* ((directory (make-temp-file "loupe" t))
         (file (expand-file-name "photo.jpg" directory))
         (loupe-proxy-directory (expand-file-name "proxies/" directory)))
    (unwind-protect
        (progn
          (write-region "one" nil file)
          (let ((before (loupe--proxy-name file)))
            (should (string-prefix-p loupe-proxy-directory before))
            (should (string-suffix-p ".jpg" before))
            (write-region "longer" nil file)
            (should-not (equal before (loupe--proxy-name file)))))
      (delete-directory directory t))))

(ert-deftest loupe-skips-proxies-for-small-or-unsuitable-files ()
  (let* ((directory (make-temp-file "loupe" t))
         (small (expand-file-name "small.jpg" directory))
         (gif (expand-file-name "anim.gif" directory))
         (loupe-proxy-directory (expand-file-name "proxies/" directory))
         (loupe-proxy-min-bytes 10)
         started)
    (unwind-protect
        (cl-letf (((symbol-function 'loupe-run-shell)
                   (lambda (command) (push command started))))
          (write-region "tiny" nil small)
          (write-region (make-string 100 ?x) nil gif)
          (should-not (loupe--proxy small))
          (should-not (loupe--proxy gif))
          (should-not started))
      (delete-directory directory t))))

(ert-deftest loupe-gallery-thumbnail-command-is-atomic-and-quoted ()
  (let* ((directory (make-temp-file "loupe" t))
         (file (expand-file-name "it's a photo.jpg" directory))
         (thumbnail (expand-file-name "thumb.png" directory))
         (image-dired-thumbnail-storage 'standard-large))
    (unwind-protect
        (progn
          (write-region "x" nil file)
          (let ((command (loupe-gallery--command file thumbnail)))
            (should (string-match-p "-auto-orient" command))
            (should (string-match-p (regexp-quote (shell-quote-argument "jpeg:size=512x512"))
                                    command))
            (should (string-match-p (regexp-quote (shell-quote-argument (concat file "[0]")))
                                    command))
            (should (string-suffix-p
                     (concat "mv -f " (shell-quote-argument (concat thumbnail ".part"))
                             " " (shell-quote-argument thumbnail))
                     command))))
      (delete-directory directory t))))

;;;; Modes

(ert-deftest loupe-mode-installs-and-removes-its-hooks-and-advice ()
  (let ((was loupe-mode))
    (unwind-protect
        (progn
          (loupe-mode 1)
          (should (memq #'loupe--image-setup image-mode-hook))
          (should (memq #'loupe--document-setup doc-view-mode-hook))
          (should (advice-member-p #'loupe--own-display 'image-get-display-property))
          (should (advice-member-p #'loupe--reset 'image-toggle-display-image))
          (loupe-mode -1)
          (should-not (memq #'loupe--image-setup image-mode-hook))
          (should-not (advice-member-p #'loupe--own-display 'image-get-display-property))
          (should-not (advice-member-p #'loupe--reset 'image-toggle-display-image)))
      (loupe-mode (if was 1 -1)))))

(ert-deftest loupe-gallery-closes-only-images-it-opened ()
  "Paging through a gallery must not kill a buffer the user already had."
  (let* ((directory (make-temp-file "loupe-gallery" t))
         (first (expand-file-name "a.txt" directory))
         (second (expand-file-name "b.txt" directory))
         (gallery (generate-new-buffer " *gallery-test*"))
         theirs opened)
    (unwind-protect
        (progn
          (write-region "a" nil first)
          (write-region "b" nil second)
          (setq theirs (find-file-noselect first))
          (with-current-buffer gallery
            (setq loupe-gallery--files (vector first second)))
          (loupe-gallery--visit gallery 0)
          (loupe-gallery--step gallery 1)
          (setq opened (current-buffer))
          (should (equal buffer-file-name second))
          (should (buffer-live-p theirs))
          (loupe-gallery--step gallery -1)
          (should (eq (current-buffer) theirs))
          (should-not (buffer-live-p opened)))
      (dolist (buffer (list theirs opened gallery))
        (when (buffer-live-p buffer) (kill-buffer buffer)))
      (delete-directory directory t))))

;;;; Emacs internals

(ert-deftest loupe-emacs-internals-are-present ()
  ;; Loupe reads Image mode's display property and winprops, advises these
  ;; functions, and uses touch-screen.el's coordinate helper.
  (dolist (function '(image-get-display-property image-toggle-display-image
                      image-toggle-display-text image-transform-set-rotation
                      image-transform-reset-to-initial image-mode-window-get
                      image-set-window-vscroll image-set-window-hscroll
                      image-display-size image-flush image-next-file
                      image-dired-thumb-name))
    (should (fboundp function)))
  (require 'touch-screen)
  (should (fboundp 'touch-screen-relative-xy))
  (should (boundp 'image-transform-rotation))
  ;; The gallery builds on Image-Dired's standard thumbnail command.
  (should (member "%f[0]" image-dired-cmd-create-standard-thumbnail-options))
  (should (member "png:%t" image-dired-cmd-create-standard-thumbnail-options)))

(provide 'loupe-test)
;;; loupe-test.el ends here
