#!/bin/bash

# unify different usernames for same person
# list of usernames was produced by
#   hg log -f -T "{author}\n" | sort | uniq
declare -A USERS
USERS["Akihisa Yamada <akihisa.yamada@uibk.ac.at>"]="Akihisa Yamada <ayamada@trs.cm.is.nagoya-u.ac.jp>"
USERS["AkihisaYamada <akihisa.yamada@uibk.ac.at>"]="Akihisa Yamada <ayamada@trs.cm.is.nagoya-u.ac.jp>"

USERS["Alexander Krauss <krauss@in.tum.de>"]="Alexander Krauss <krauss@in.tum.de>"
USERS["krauss"]="Alexander Krauss <krauss@in.tum.de>"

USERS["Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at>"]="Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at>"

USERS["Carsten Fuhs <fuhs@informatik.rwth-aachen.de>"]="Carsten Fuhs <fuhs@informatik.rwth-aachen.de>"

USERS["Christian Sternagel"]="Christian Sternagel <c.sternagel@gmail.com>"
USERS["griff"]="Christian Sternagel <c.sternagel@gmail.com>"

USERS["csag9384"]="Thomas Sternagel <thomas.sternagel@uibk.ac.at>"
USERS["Thomas Sternagel"]="Thomas Sternagel <thomas.sternagel@uibk.ac.at>"

USERS["gallais"]="Guillaume Allais"
USERS["hzankl"]="Harald Zankl"

USERS["Julian Nagele <csag8264@uibk.ac.at>"]="Julian Nagele <julian.nagele@uibk.ac.at>"
USERS["Julian Nagele <julian.nagele@uibk.ac.at>"]="Julian Nagele <julian.nagele@uibk.ac.at>"

USERS["Martin Avanzini <martin.avanzini@uibk.ac.at>"]="Martin Avanzini <martin.avanzini@uibk.ac.at>"

USERS["rene@colo2-c703.uibk.ac.at"]="René Thiemann <rene.thiemann@uibk.ac.at>"
USERS["Rene Thiemann <rene.thiemann@uibk.ac.at>"]="René Thiemann <rene.thiemann@uibk.ac.at>"
USERS["René Thiemann <rene.thiemann@uibk.ac.at>"]="René Thiemann <rene.thiemann@uibk.ac.at>"
USERS["Ren√© Thiemann <rene.thiemann@uibk.ac.at>"]="René Thiemann <rene.thiemann@uibk.ac.at>"

USERS["Sarah Winkler <sarah.winkler@uibk.ac.at>"]="Sarah Winkler <sarah.winkler@uibk.ac.at>"
USERS["swinkler"]="Sarah Winkler <sarah.winkler@uibk.ac.at>"

USERS["wenzelm"]="Makarius Wenzel <makarius@sketis.net>"

# get list of authors and modification years for a given file
function authoryears()
{ 
  local IFS=$'\n'
  for info in $(hg log -f -T "{author},{date|shortdate}\n" "$1")
  do
    AUTHOR=$(echo "$info" | sed "s/\(.*\),.*/\1/")
    YEAR=$(date -d "$(echo "$info" | sed "s/.*,\(.*\)/\1/")" +"%Y")
    echo "${USERS["$AUTHOR"]},${YEAR}"
  done | sort | uniq
}

# map author names to list of modification years 
declare -A DATA

function setdata()
{
  local IFS=$'\n'
  for x in $(authoryears "$1")
  do
    AUTHOR=$(echo "$x" | sed "s/\(.*\),.*/\1/")
    YEAR=$(echo "$x" | sed "s/.*,\(.*\)/\1/")
    if [ ${DATA["$AUTHOR"]+_} ]
    then
      DATA["$AUTHOR"]="${DATA[$AUTHOR]} $YEAR"
    else
      DATA["$AUTHOR"]="$YEAR"
    fi
  done
}

# collapse a list of numbers "1, 2, ..., n" into the range "1-n"
function range()
{
  if [[ ${#@} -gt 2 ]]
  then
    n=${#@}
    echo "$1-${!n}"
  else
    echo "${@}" | sed 's/\s\s*/, /g'
  fi
}

# compress year-information into ranges
function rangedata()
{
  local IFS=$' \t\n'
  for x in "${!DATA[@]}"
  do
    DATA["$x"]=$(range ${DATA["$x"]})
  done
}

function header()
{
  local IFS=$'\n'
  unset DATA
  declare -A DATA
  setdata "$1"
  rangedata
  for x in "${!DATA[@]}"
  do
    printf "Author:  %s (%s)\n" "$x" "${DATA["$x"]}"
  done | sort
  printf "License: LGPL (see file COPYING.LESSER)\n"
}

function addauthorinfo()
{
  for f in "$@"
  do
    if [[ -f $f ]]
    then
      echo "adding author-info to file $f ..."
      ext=${f##*.}
      bc=""
      ec=""
      # set appropriate multiline comment markers
      case ${ext} in
        hs) 
          bc='{-'
          ec='-}'
        ;;
        ml|ML)
          bc='(*'
          ec='*)'
        ;;
        scala)
          bc='/*'
          ec='*/'
        ;;
        thy)
          bc='(*'
          ec='*)'
        ;;
        *)
          echo "illegal extension: ${ext}" >&2
          exit 1
        ;;
      esac
      cat "$f" > "$f.tmp"
      {
        echo "${bc}"
        header "$f"
        echo "${ec}"
        cat "${f}.tmp"
      } > "$f"
      rm "${f}.tmp"
    fi
  done
}

