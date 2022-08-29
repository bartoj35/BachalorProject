#!/bin/bash

sudo apt install opam;		# install opam package manager

opam init;					# init opam package manager
eval $(opam env);			# init opam enviroment

opam install depext;		# install package for dependences
opam depext frama-c;		# install frama dependences
opam install frama-c;		# install frama itself

eval $(opam env);			# update opam enviroment
