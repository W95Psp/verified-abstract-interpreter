(
 (
  fstar-mode . (
		(eval . (progn
			  (setq-local
			   fstar-subp-prover-args '()
			   )
			  (setq-local
			   prettify-symbols-alist
			   (append
			    fstar-symbols-alist
			    '(("gamma" . ?γ))
			    )
			   )
			  (sit-for 0)
			  (prettify-symbols-mode)
			  )
		      )
		)))
