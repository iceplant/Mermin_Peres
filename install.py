#!/bin/bash
# My first script

#echo "Hello World!"

#Install Homebrew
/usr/bin/ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"


#Lean installation
# git clone https://github.com/leanprover/lean
# cd lean
# mkdir -p build/release
# cd build/release
# cmake ../../src
# make

# git clone https://github.com/leanprover/lean
# cd lean
# mkdir -p build/debug
# cd build/debug
# cmake -D CMAKE_BUILD_TYPE=DEBUG ../../src
# make

#Mathlab installation
brew install gmp coreutils
curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh



source $HOME/.elan/env
brew install python3
sudo pip3 install mathlibtools

leanpkg new my_project3
 cd my_project3
 leanpkg add leanprover-community/mathlib
 update-mathlib

#tutorial project installation
git clone https://github.com/leanprover-community/tutorials.git
cd tutorials
leanpkg configure
update-mathlib
leanpkg build