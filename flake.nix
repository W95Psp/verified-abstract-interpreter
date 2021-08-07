{
  description = "LiterateFStar";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-20.09";    
    fstar-flake.url = "github:W95Psp/nix-flake-fstar";
    zarith_stubs_js = {
      url = "github:janestreet/zarith_stubs_js";
      flake = false;
    };
  };
  
  outputs = { self, nixpkgs, flake-utils, fstar-flake, zarith_stubs_js }:
    flake-utils.lib.eachSystem [ "x86_64-darwin" "x86_64-linux" "aarch64-linux"]
      (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          fstar-o = fstar-flake.packages.${system}.fstar;
          tools = fstar-flake.lib.${system}.fstar;
          lib = pkgs.lib;
          pygments = pkgs.python37Packages.pygments.overrideAttrs (_:
            { pname = "Pygments"; version = "master-060520";
              src = pkgs.fetchFromGitHub {
                owner = "pygments"; repo = "pygments";
                rev = "d090c0be255cc2eef02637e2bebeaab4b5fa9ddd";
                sha256 = "1b2j3x3fcz23cn073zq6v057ckdj0bxm80iby7r0jlqcgasl6r48";
              };});
          fst-sources = path: lib.cleanSourceWith {
            src = path;
            filter = path: kind: kind == "directory"
                              || pkgs.lib.hasSuffix ".fst" path
                              || pkgs.lib.hasSuffix ".js" path
                              || pkgs.lib.hasSuffix ".checked" path
                              || pkgs.lib.hasSuffix ".fsti" path
                              || pkgs.lib.hasSuffix "/Makefile" path;
          };
        in
          rec {
            packages = {
              paper-sources = fst-sources ./.;
              fstar =
                tools.perform-fstar-to-ocaml fstar-o
                  (fstar-o.overrideAttrs 
                    (o: {patches = o.patches ++ [./patches/restore-unicode.patch];}));
              tests = pkgs.stdenv.mkDerivation {
                name = "AbIntFStar-tests"; src = ./tests;
                buildPhase = ''ANALYSER_BINARY='${packages.analyser}/analyser' make | tee logs'';
                installPhase = ''cp logs $out'';
              };
              typecheck = pkgs.stdenv.mkDerivation {
                name = "AbIntFStar-typecheck"; src = fst-sources ./.;
                buildInputs = [packages.fstar pkgs.gnumake];
                buildPhase = ''cd src/; make 2>&1 | tee fstar.log'';
                installPhase = "cp fstar.log $out";
              };
              latex = pkgs.stdenv.mkDerivation {
                name = "AbIntFStar-latex"; src = fst-sources ./.;
                buildInputs = [pkgs.nodejs];
                buildPhase = ''node latex/extract.js latex/LaTeX.Entrypoint.fst > main.tex'';
                installPhase = "cp main.tex $out";
              };
              all = pkgs.stdenv.mkDerivation {
                name = "AbIntFStar";
                unpackPhase = "true";
                buildPhase = "true";
                installPhase = ''
                  mkdir -p $out/bin
                  cd $out
                  cp --no-preserve=mode -r '${./tests}' examples
                  (echo "ANALYSER_BINARY := \"$out/bin/analyser\""; cat '${./tests}/Makefile') > examples/Makefile
                  cp ${packages.pdf} paper.pdf
                  cp ${packages.latex} paper.tex
                  cp ${packages.analyser}/analyser bin/analyser
                  cp -r ${packages.js-analyser} webapp/
                  cp ${packages.tests} test-report.log
                  cp ${packages.typecheck} typechecking.log
                '';
              };
              pdf = pkgs.stdenv.mkDerivation {
                name = "AbIntFStar-pdf";
                src = lib.cleanSourceWith {
                  src = ./.;
                  filter = path: kind: kind == "directory"
                                    || pkgs.lib.hasSuffix ".cls" path
                                    || pkgs.lib.hasSuffix "orcid.pdf" path
                                    || pkgs.lib.hasPrefix (toString ./latex) path;
                };
                buildInputs = with pkgs; [
                  gnused gnugrep findutils toybox bash latexrun which ncurses pygments dejavu_fonts
                  (with pkgs.texlive; texlive.combine ({
                    inherit (texlive) scheme-basic fontspec minted glossaries enumitem pgf xcolor biblatex mathtools 
                      unicode-math ec soul platex-tools appendix glossaries-english bookmark acmart microtype wrapfig
                      environ metafont fvextra fancyvrb upquote lineno catchfile xstring framed float mfirstuc todonotes
                      textcase xfor datatool csquotes xpatch newunicodechar collection-fontsextra stmaryrd todo totpages breakurl
                      cleveref;
                  }))];
                buildPhase = ''latexrun --clean-all; latexrun --latex-args="-shell-escape" ${packages.latex}'';
                installPhase = ''cp *.pdf $out'';
              };
              arxiv = packages.pdf.overrideAttrs (o: {
                buildInputs = o.buildInputs ++ (with pkgs; [gnutar sd]);
                buildPhase = ''
                  cp ${packages.latex} main.tex
                  sd '(\\usepackage\[)outputdir=latex.out[^]]*(\]\{minted\})' '$1$2' latex/preamble.tex
                  echo "## Generate minted cache by compiling with 'finalizecache'"
                  latexrun -O . --latex-args="-shell-escape" main.tex
                  sd '(\\usepackage\[)[^]]*(\]\{minted\})' '$1,finalizecache$2' latex/preamble.tex
                  latexrun -O . --max-iterations 2 --latex-args="-shell-escape" main.tex || true

                  echo "## Add 'frozencache' option, and try to recompile without '--shell-escape'"
                  sd '(\\usepackage\[)[^]]*(\]\{minted\})' '$1,frozencache$2' latex/preamble.tex
                  # latexrun -O . main.tex
                  
                  echo "## All good!"
                '';
                installPhase = ''
                  find . \( \(                                     \
                      -type f                                   \
                      ! \(   -name 'orcid.pdf' -o -name '*.bst' \
                          -o -name '*.cls' -o -name '*.glo'     \
                          -o -name '*.tex' -o -name '*.pyg*'    \
                          -o -name '*.ind' -o -name '*.bbl'     \
                        \)                                      \
                    \) -o \( -type d -empty \) \) -delete
                  
                  tar -czf $out *
                '';
              });
              ocaml = pkgs.stdenv.mkDerivation {
                name = "analyser-ocaml"; src = fst-sources ./.;
                buildInputs = [ packages.fstar ];
                buildPhase = ''
                cd src ; rm -rf ./out/
                fstar.exe --include app/StarCombinator --include app/PrettyPrinter --include app --include core --admit_smt_queries true --extract '* -LaTeX -LaTeX.Entrypoint -FStar' --odir out --codegen OCaml Main.fst
                '';
                installPhase = "mkdir $out && cp -r ./out/* $out/";
              };
              js-analyser =
                pkgs.stdenv.mkDerivation {
                name = "analyser-js"; unpackPhase = "true";
                buildInputs = with pkgs.ocamlPackages;
                  [ js_of_ocaml js_of_ocaml-ppx ocaml ocamlbuild findlib ppx_deriving 
                    pprint ppx_deriving_yojson zarith stdint batteries pkgs.sd];
                buildPhase = ''
                cp -r ${packages.ocaml}/* .
                export OCAMLPATH="$OCAMLPATH:${packages.fstar}/bin"
                sd -s COMPILATION_TIMESTAMP "$(date +'%Hh%M_%d-%m-%+4Y')" Main.ml
                # OCaml is not happy with 'ⵌ' begin part of indentifiers
                sd '([a-z])ⵌ' 'ab_$1' *.ml
                cat ${./src/js/Driver.ml} > Driver.ml
                ocamlbuild -lflags '-w -31' -use-ocamlfind -package fstarlib -package js_of_ocaml -package js_of_ocaml-ppx Driver.byte
                js_of_ocaml ${zarith_stubs_js}/biginteger.js ${zarith_stubs_js}/runtime.js Driver.byte --disable genprim
                cat  ${./src/js/compat.js} Driver.js > analyser.js
                '';
                installPhase = ''mkdir $out
                                 cp analyser.js $out/analyser.js
                                 ( 
                                   # ship tests
                                   printf "<script>\nlet tests = "
                                   cat ${pkgs.writeTextFile {
                                     name = "tests.json";
                                     text = builtins.toJSON (pkgs.lib.mapAttrs (n: _: builtins.readFile (./tests + ("/" + n))) (pkgs.lib.filterAttrs (n: _:pkgs.lib.hasSuffix ".c" n) (builtins.readDir ./tests)));
                                   }}
                                   echo "</script>"
                                   cat ${./src/js/index.html}
                                 ) > $out/index.html
                                 cp ${./src/js/ansi_up.js} $out/ansi_up.js
                                 '';
              };
              analyser = pkgs.stdenv.mkDerivation {
                name = "analyser-bin"; unpackPhase = "true";
                buildInputs = (with pkgs.ocamlPackages;
                  [ ocaml ocamlbuild findlib ppx_deriving
                    pprint ppx_deriving_yojson zarith stdint batteries pkgs.sd]);
                buildPhase = ''
                cp -r ${packages.ocaml}/* .
                export OCAMLPATH="$OCAMLPATH:${packages.fstar}/bin"
                sd -s COMPILATION_TIMESTAMP "$(date +'%Hh%M_%d-%m-%+4Y')" Main.ml
                # OCaml is not happy with 'ⵌ' begin part of indentifiers
                sd '([a-z])ⵌ' 'ab_$1' *.ml
                echo "let _ = exit (if Main.main (Array.to_list Sys.argv) then 0 else 1)" > Driver.ml
                ocamlbuild -package fstarlib Driver.native'';
                installPhase = ''
                   mkdir $out 
                   cp Driver.native $out/analyser
                '';
              };
              webapp-server =
                pkgs.writeScriptBin "httpserver" ''#!${pkgs.stdenv.shell}
                   cd ${packages.js-analyser}
                   echo "Listening on port 8251"
                   ${pkgs.webfs}/bin/webfsd -F -p 8251 -f index.html
                '';
              webapp-nix-shell = pkgs.mkShell rec {
                name = "webapp-nix-shell";
                buildInputs = [packages.webapp-server];
              };
              preconfigured-emacs =
                pkgs.writeScriptBin "preconfigured-emacs"
                  ''#!${pkgs.stdenv.shell}
                    export PATH="${packages.fstar}/bin:$PATH"
                    export EMACSLOADPATH=
                    export HOME=$(mktemp -d)
                    ${(pkgs.emacsPackagesGen pkgs.emacs).emacsWithPackages (epkgs: with epkgs.melpaPackages; [
                      fstar-mode
                      (pkgs.runCommand "default.el" {} ''
                                   mkdir -p $out/share/emacs/site-lisp
                                   cp ${pkgs.writeText "default.el" ''
                                            (setq inhibit-startup-buffer-menu t)
                                            (add-hook 'window-setup-hook 'delete-other-windows)
                                            (setq enable-local-eval t)
                                      ''} $out/share/emacs/site-lisp/default.el'')
                    ])}/bin/emacs --no-splash "$@" src/core/*.fst src/core/LangDef.fst'';
            };
            apps = {
              emacs = { type = "app";
                        program = "${packages.preconfigured-emacs}/bin/preconfigured-emacs";
                      };
              webapp = { type = "app";
                         program = "${packages.webapp-server}/bin/httpserver"; };
              make-gh-pages = {
                type = "app";
                program = "${pkgs.writeScript "mkdist" ''
                    #!${pkgs.stdenv.shell}
                    ${pkgs.git}/bin/git diff --staged --cached --quiet || {
                      echo "There is some staged files: abort"
                      exit 1
                    }
                    rm -rf dist
                    cp --no-preserve=mode -r ${packages.all} dist
                    ${pkgs.git}/bin/git add dist
                    ${pkgs.git}/bin/git commit -m 'dist update'
                    ${pkgs.git}/bin/git subtree split --prefix dist/webapp -b webapp-dist
                    ${pkgs.git}/bin/git push -f origin webapp-dist:webapp-dist
                    ${pkgs.git}/bin/git branch -D webapp-dist
                    ${pkgs.git}/bin/git push
                ''}";
              };
            };
            devShell = pkgs.mkShell rec {
              name = "compile-env";
              buildInputs = with pkgs.ocamlPackages;
                [ ocaml ocamlbuild findlib ppx_deriving pprint ppx_deriving_yojson zarith stdint batteries
                  packages.fstar packages.preconfigured-emacs
                ];
              shellHook = ''export OCAMLPATH="$OCAMLPATH:${fstar-o}/bin"'';
            };
            defaultPackage = packages.analyser;

          }
      );
}
