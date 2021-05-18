{ stdenv, pkgs, fetchzip, fetchpatch, fetchgit, fetchurl }:
stdenv.mkDerivation {
  name = "text";

  src = ./. ;
  buildInputs = with pkgs;
  [ ats2
    gcc
    which
    libunistring
  ];

}
