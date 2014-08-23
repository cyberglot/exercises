#!/bin/bash

set -e

sudo apt-get update -y -qq

install-isabelle() {
  # Download and extract Isabelle
  cd /tmp
  wget "http://isabelle.in.tum.de/dist/Isabelle2013-2_linux.tar.gz"
  tar xf Isabelle2013-2_linux.tar.gz
  # Build the built-in logic images
  ./Isabelle2013-2/bin/isabelle build -bv HOL
  # Install Isabelle
  sudo mv Isabelle2013-2 /opt
  sudo chown -R root:root /opt/Isabelle2013-2
  sudo /opt/Isabelle2013-2/bin/isabelle install /usr/local/bin
}

install-coq() {
  cd /tmp
  wget "http://coq.inria.fr/distrib/V8.4pl4/files/coq-8.4pl4.tar.gz"
  tar xf coq-8.4pl4.tar.gz
  cd coq-8.4pl4
  ./configure -prefix /usr/local
  make
  sudo make install
}

case "${EXERCISES}" in
  concrete-semantics)
    # Install Isabelle for Concrete Semantics exercises
    sudo apt-get install lib32stdc++6 # PolyML is faster on 32 bit
    install-isabelle;;
  software-foundations)
    sudo apt-get install ocaml-native-compilers camlp5
    install-coq;;
esac
