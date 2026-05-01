{ pkgs ? import <nixpkgs> { system = builtins.currentSystem; } }:

pkgs.mkShell rec {
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

  packages = with pkgs; [
    (python3.withPackages (ps: with ps; [
      lab
    ]))
    txt2tags # Not propagated?

    cmake
    gcc
    kissat
  ];

  shellHook = ''
    export PATH="$PATH:$HOME/thesis/VAL"
    export DOWNWARD_REPO=$HOME/thesis/downward-sat
    export DOWNWARD_BENCHMARKS=$HOME/thesis/classical-domains/classical
  '';
}
