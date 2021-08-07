(
 (
  fstar-mode . (
		(eval . (progn
			  (setq-local
			   fstar-subp-prover-args '("--include" "StarCombinator"
						    "--include" "PrettyPrinter"
						    "--include" "../core")
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
