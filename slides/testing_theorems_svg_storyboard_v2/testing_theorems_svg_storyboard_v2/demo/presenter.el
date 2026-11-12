;;; presenter.el --- Prepare the QuickChick demo for projection -*- lexical-binding: t; -*-

(defconst quickchick-demo-file
  (file-truename
   (or (getenv "QUICKCHICK_DEMO_FILE")
       (expand-file-name "STLCBugDemo.v"
                         (file-name-directory (or load-file-name buffer-file-name))))))

(defvar quickchick-demo-ready nil)

(setq inhibit-startup-screen t
      initial-scratch-message nil
      ring-bell-function #'ignore
      proof-splash-enable nil
      proof-three-window-mode-policy 'hybrid)

;; Use one large, quiet frame.  Changing the default face also enlarges the
;; goals and response panes that Proof General opens later.
(when (display-graphic-p)
  (set-frame-parameter nil 'fullscreen 'maximized))
(set-face-attribute 'default nil :height 220)
(setq-default line-spacing 0.12)
(when (fboundp 'tool-bar-mode) (tool-bar-mode -1))
(when (fboundp 'scroll-bar-mode) (scroll-bar-mode -1))
(when (fboundp 'tooltip-mode) (tooltip-mode -1))

(defun quickchick-demo--show-theorem (buffer target)
  "Show BUFFER at TARGET after Proof General has finished its queue."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (goto-char target)
      (setq cursor-type 'box)
      (setq proof-three-window-enable t)
      (when (fboundp 'display-line-numbers-mode)
        (display-line-numbers-mode -1))
      (switch-to-buffer buffer)
      (delete-other-windows)
      (recenter 4)
      (setq quickchick-demo-ready t)
      (message "Demo ready.  Use C-c C-n to step through the theorem."))))

(defun quickchick-demo--wait-for-proof-general (buffer target tries)
  "Wait for Proof General to process BUFFER through TARGET."
  (when (buffer-live-p buffer)
    (with-current-buffer buffer
      (if (or (<= tries 0)
              (and (boundp 'proof-action-list)
                   (null proof-action-list)
                   (boundp 'proof-shell-busy)
                   (not proof-shell-busy)))
          (quickchick-demo--show-theorem buffer target)
        (run-at-time 0.15 nil
                     #'quickchick-demo--wait-for-proof-general
                     buffer target (1- tries))))))

(defun quickchick-demo-prepare ()
  "Process the setup and stop immediately before `Theorem preservation'."
  (when (and buffer-file-name
             (string= (file-truename buffer-file-name) quickchick-demo-file))
    (goto-char (point-min))
    (unless (search-forward "Theorem preservation" nil t)
      (user-error "Could not find the preservation theorem"))
    (beginning-of-line)
    (let ((target (point))
          (buffer (current-buffer)))
      (message "Preparing the QuickChick demo...")
      ;; Keep setup output from rearranging the frame.  Three-pane mode is
      ;; restored before the presenter begins stepping through the theorem.
      (setq proof-three-window-enable nil)
      (proof-goto-point)
      (run-at-time 0.15 nil
                   #'quickchick-demo--wait-for-proof-general
                   buffer target 400))))

(add-hook 'find-file-hook #'quickchick-demo-prepare)

;;; presenter.el ends here
