{ pkgs ? import <nixpkgs> { system = builtins.currentSystem; } }:

let
  lab = pkgs.python3.pkgs.buildPythonPackage rec {
    pname = "lab";
    version = "8.9";
    format = "wheel";

    src = pkgs.fetchPypi {
      inherit pname version format;
      sha256 = "2f59f577df8928185540dcda0047e6362257b1ed7c62bfe48a06affa3ac0d980";
      python = "py3";
      dist = "py3";
    };

    propagatedBuildInputs = with pkgs.python3Packages; [
      matplotlib
      simplejson
    ] ++ [
      pkgs.txt2tags
    ];
  };
  validate = pkgs.stdenv.mkDerivation rec {
    pname = "VAL";
    version = "4";

    src = pkgs.fetchgit {
      url = "https://github.com/KCL-Planning/VAL.git";
      rev = "a5565396007eee73ac36527fbf904142b3077c74";
      hash = "sha256-5B9qW9HS9YcEmmunCS1qB/N6xOnlM1dP0Qj8Jrm23sU=";
    };

    nativeBuildInputs = with pkgs; [
      autoPatchelfHook
    ];

    buildInputs = with pkgs; [
      flex
      bison
      gcc.cc.lib
    ];

    buildPhase = ''
      runHook preBuild

      # There are binaries in the repo at a556539
      make clean
      sed -i 's/-Werror //g' Makefile
      make validate

      runHook postBuild
    '';

    installPhase = ''
      runHook preInstall

      mkdir -p $out/bin
      cp validate $out/bin
      chmod u+x $out/bin/validate

      runHook postInstall
    '';
  };
in
pkgs.mkShell {
  packages = with pkgs; [
    (python3.withPackages (ps: with ps; [
      lab
    ]))
    txt2tags # Not propagated?

    cmake
    gcc
    kissat

    validate
  ];

  shellHook = ''
    export DOWNWARD_REPO=$PWD/..
    export DOWNWARD_BENCHMARKS=$PWD/../../benchmarks/
  '';
}
