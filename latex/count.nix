{pkgs ? import <unstable> {}}:
let
  to-compare = {
    lattice-lib = {
      src = fetchTarball http://people.irisa.fr/David.Pichardie/ext/lattice/all.tgz;
      pre = "true";
      langs = ["Coq"];
    };
    value-analysis = {
      src = fetchTarball http://www.irisa.fr/celtique/ext/value-analysis/value-analysis.tgz;
      pre = "cd vanalysis";
      langs = ["Coq"];
    };
    jvm-iflow = {
      src = fetchTarball http://people.irisa.fr/David.Pichardie/ext/iflow/jvm_iflow_coq.tgz;
      pre = "true";
      langs = ["Coq"];
    };
    verasco = {
      src = fetchTarball http://compcert.inria.fr/verasco/release/verasco-1.3.tgz;
      pre = "cd verasco";
      langs = ["Coq"];
    };
    "ITP10:Cachera:Pichardie" = {
      src = fetchTarball https://people.irisa.fr/David.Pichardie/ext/itp10/certified_while.tgz;
      pre = "true";
      langs = ["Coq"];
    };
    dataflow-analyser = {
      src = fetchTarball https://web.archive.org/web/20051122093937if_/http://www.irisa.fr:80/lande/pichardie/CarmelCoq/SAS05/all.tgz;
      pre = "true";
      langs = ["Coq"];
    };
    self = {
      src = ../src/core;
      pre = "true";
      langs = ["F*"];
    };
  };
  stats = builtins.mapAttrs (name: {src, pre, langs}:
    pkgs.stdenv.mkDerivation {
      name = name + ".count";
      inherit src;
      buildInputs = [pkgs.tokei pkgs.jq];
      configurePhase = "true";
      buildPhase = "true";
      installPhase = ''
        ${pre}
        tokei -o json | jq -r '${pkgs.lib.concatMapStringsSep " + " (x: ''.["${x}"].code'') langs}' >> $out
      '';
    }
  ) to-compare;
  res = builtins.mapAttrs (_: d: pkgs.lib.toInt (builtins.readFile d)) stats;
in
pkgs.writeTextFile {
  name = "count.json";
  text = builtins.toJSON (
    pkgs.lib.mapAttrs (k: v: {lines = v; factor = v / (res.self + 0.0);}) res
  );
}

