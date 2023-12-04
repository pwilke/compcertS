let pkgs =import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/refs/tags/17.09.tar.gz") {};
in
with pkgs;

let
my_ppsimpl = pkgs.stdenv.mkDerivation {
      name = "my-coq-ppsimpl-8.4";
      src = pkgs.fetchgit { url = https://gitlab.inria.fr/fbesson/ppsimpl.git;
      rev = "b9472cb3a7f9675010913f6293742e3ebc4c2a8b";
      sha256 = "0p2d3aw2cvz1yiy03vq0vv84mczn28hb7ivh2a5sd0qrsl9l595r";
      };
    buildInputs = [ pkgs.which pkgs.coq_8_4.ocaml pkgs.coq_8_4.camlp5 ];
    propagatedBuildInputs = [ pkgs.coq_8_4 ];
    installFlags = "COQLIB=$(out)/lib/coq/8.4/"; #${pkgs.coq.coq-version}/";
   };
   in

stdenv.mkDerivation {

  name = "scc";

  buildInputs = with ocamlPackages_4_01_0; [
    ocaml menhir my_ppsimpl coq_8_4 z3 findlib 
  ];

}
