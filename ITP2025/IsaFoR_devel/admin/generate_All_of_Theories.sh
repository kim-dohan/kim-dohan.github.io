#!/bin/bash

# Script to generate the All_of_... theory files.

echo
echo "The All_of_... theories will only list CLEAN theory files in the repo!"
echo 

set -e

test -d thys || (echo "This command should be executed in the IsaFoR main directory"; exit 1)
test -f thys/Proof_Checker/Version.thy || (echo "Make sure that Version.thy has been generated"; exit 1)

DIRS="AC_Rewriting Abstract_Completion Auxiliaries Conditional_Rewriting Confluence_and_Completion Framework LTS Nonreachability Nontermination Normalization_Equivalence Orderings Proof_Checker Rewriting Semantic_Labeling Termination_and_Complexity Tree_Automata"

cd thys
for dir in $DIRS; do 
  hg st -ci $dir/*.thy | # only consider clean (and ignored for Version.thy) theory files
  sed -e 's/^.*\/\(.*\)\.thy.*/    \1/' | # extract file names without .thy
  grep -v "All_of_$dir" | # exclude any existing All_of_... file
  sed -e "1s/^/(* Automatically generated file, do not change *)|theory All_of_$dir|  imports|/" | # write header
  sed -e '$s/$/|begin|end/' | # write footer
  tr '|' '\n' > $dir/All_of_$dir.thy && # replace | by newline
  echo "wrote $dir/All_of_$dir.thy"; 
done
