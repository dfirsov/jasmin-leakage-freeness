((easycrypt-mode .
  ((eval .
    (cl-flet ((pre (s) (concat (locate-dominating-file buffer-file-name ".dir-locals.el") s)))
      (setq easycrypt-load-path `(,(pre ".")))
      (setq easycrypt-prog-args
	    `( "-emacs", "-pp-width", "120"
             , "-I", (pre ".")
	     , "-I", (pre "auxiliary_lemmas")
	     , "-I", (pre "big_num_ops")
             , "-I", (pre "big_num_ops/leakage_freeness")
             , "-I", (pre "random_bit")
             , "-I", (pre "random_bit/leakage_freeness")
             , "-I", (pre "jasmin_extracts")
             , "-I", (concat "Jasmin:" (pre "eclib"))
             , "-I", (concat "RealJasmin:" "/Users/jba/src/jasmin/eclib/")
      ))
)))))
