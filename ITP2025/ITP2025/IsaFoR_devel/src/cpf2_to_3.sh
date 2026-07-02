#!/bin/bash
# converts CPF 2 file to CPF 3
# usage: ./cpf2_to_3.sh [--termIndex] [cpf2.xml | - ]

DIR=$(dirname "$(readlink -f "$0")")

${DIR}/cpf2_to_3_phase_1 $* | xsltproc --huge --maxdepth 100000 ${DIR}/xml/cpf2_to_3.xsl - 
