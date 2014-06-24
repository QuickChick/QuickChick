((coq-mode . (
   ;; HACK: Include everything at two levels, so that relative paths
   ;; make sense when editing a file at either level.
   (coq-load-path . ("../Machine" "../Testing")))))

;; ((coq-mode . ((coq-load-path . ("../Testing" "../Machine" ... ))))) 

;; ((coq-mode
;;   . ((eval . 
;; 	   (progn
;; 	     (make-local-variable 'coq-prog-args)
;; 	     (setq coq-prog-args `("-emacs"
;; 				  "-R" , (expand-file-name (locate-dominating-file buffer-file-name ".dir-locals.el")) "Testing" )))))))
