
;; FIXME: it would probably be better to use some built-in Emacs-y
;; customisation stuff to do this bit. And to rewrite
;; transition-function to use it without having this indirection.
(defun $modename$-classification-to-face (classification)
  (cond ((eq classification 'comment)     'font-lock-comment-face)
	((eq classification 'keyword)     'font-lock-keyword-face)
	((eq classification 'punctuation) 'font-lock-variable-name-face)
	((eq classification 'identifier)  'default)
	((eq classification 'whitespace)  'default)
	((eq classification 'constant)    'font-lock-constant-face)
	((eq classification 'operator)    'font-lock-keyword-face)
	((eq classification 'constructor) 'font-lock-constant-face)
        ((eq classification 'type)        'font-lock-type-face)))

;; lexer state consists of:
;;   the start of the current lexeme
;;   the current state
;;   the last good match (optional)

;; for each character, update the current state by applying the
;; transition-function.
;;   on error:  if we have a last good match, go for it and apply the appropriate property
;;              if no match, report error
;;   on move:   just move to the new state
;;   on accept: record the new match and move to the new state
(defun $modename$-lex-buffer ()
  (interactive)
  (message "Lexing...")
  (setq $modename$-lexing-timer nil)
  (setq $modename$-lexing-underway t)
  (catch 'abort-lexing
    (with-silent-modifications
     (let ((position       1)
	   (final-position (+ (buffer-size) 1))
	   (state          0)
	   (lexeme-start   1)
	   (current-match  nil))
       (while (<= position final-position)
	 (cond ((and (= (mod position 200) 0) (input-pending-p))
		($modename$-schedule-lexing)
		(throw 'abort-lexing t))
	       ((= position final-position)
		(cond ((= lexeme-start position)
		       (setq position (1+ position)))
		      ((null current-match)
		       (progn
			 (message "Lexing failure at EOF")
			 (put-text-property lexeme-start final-position 'face 'default)
			 (put-text-property lexeme-start final-position 'face '(:underline "red"))
			 (throw 'abort-lexing t)))
		      (t
		       (let ((lexeme-end  (car current-match))
			     (lexeme-type (cdr current-match)))
			 (put-text-property lexeme-start lexeme-end 'face ($modename$-classification-to-face lexeme-type))
			 (setq position lexeme-end)
			 (setq current-match nil)
			 (setq state 0)
			 (setq lexeme-start position)))))
	       (t
		(let ((result ($modename$-transition-function state (char-after position))))
		  (cond ((eq (car result) 'change)
			 (setq state (car (cdr result)))
			 (setq position (1+ position)))
			((eq (car result) 'accept)
			 (setq position (1+ position))
			 (setq state (car (cdr result)))
			 (setq current-match (cons position (car (cdr (cdr result))))))
			((eq (car result) 'error)
			 (if (null current-match)
 			     ;; Lexing failure, abort. FIXME: attempt to determine what states were reachable from the previous state
			     (progn
			       (message (format "Lexing failure at position %d" position))
			       (put-text-property lexeme-start final-position 'face 'default)
			       (put-text-property lexeme-start final-position 'face '(:underline "red"))
			       (throw 'abort-lexing t))
			   ;; Lexing success
			   (let ((lexeme-end  (car current-match))
				 (lexeme-type (cdr current-match)))
			     (put-text-property lexeme-start lexeme-end 'face ($modename$-classification-to-face lexeme-type))
			     (setq position lexeme-end)
			     (setq current-match nil)
			     (setq state 0)
			     (setq lexeme-start position)))))))))))
    (message "Finished Lexing"))
  (setq $modename$-lexing-underway nil))

(defvar $modename$-lexing-timer nil)
(make-variable-buffer-local '$modename$-lexing-timer) ;; FIXME: apparently this is the wrong way to do it

(defvar $modename$-lexing-underway nil)
(make-variable-buffer-local '$modename$-lexing-underway)

(defsubst $modename$-schedule-lexing ()
  "Schedule a new lexing job"
  (if $modename$-lexing-timer
      (cancel-timer $modename$-lexing-timer))
  (setq $modename$-lexing-timer
	(run-with-idle-timer 0.2 nil #'$modename$-lex-buffer))) ;; FIXME: abstract out the delay here

(defun $modename$-do-lexing (start end len)
  (if (not $modename$-lexing-underway)
      ($modename$-schedule-lexing)))

(defun $modename$-mode ()
  "Major mode for editing $modename$ programs"
  (interactive)
  (kill-all-local-variables)
  (setq major-mode '$modename$-mode)
  (setq mode-name "$modename$")
  (set-input-method "TeX")

  ($modename$-lex-buffer)
  (add-hook 'after-change-functions '$modename$-do-lexing nil t)
;  (run-mode-hooks)
)

;; FIXME: set indent-line-function to something useful
;; FIXME: setup a keymap
;; FIXME: check the stuff about making variables buffer local

;(defun uninstall-lexing ()
;  (interactive)
;  (remove-hook 'after-change-functions 'do-lexing t))

(add-to-list 'auto-mode-alist
	     '("$fileregexp$" . $modename$-mode))
