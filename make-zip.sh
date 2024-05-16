#!/usr/bin/env bash
set -euo pipefail
IFS=$'\n\t'

if [ -x "$(command -v gsed)" ]; then
    SED=gsed
else
    SED=sed
fi


NAME=pldi24-36-artifact

# not used for compilation
EXCLUDE=(
    .gitattributes
    .gitignore
    .gitlab-ci.yml
    .ignore
    make-package
    make-zip.sh
    build-docker.sh
)

rm -rf $NAME $NAME.zip

git clone -b omo --single-branch --depth 1 ssh://git@git.fearless.systems:9001/kaist-cp/verification/irc11.git $NAME

# remove excluded files
for f in "${EXCLUDE[@]}"; do
    rm -r $NAME/$f
    $SED -i -E -e "\:${f}:d" $NAME/_CoqProject
done

# # anonymize opam package definition
# $SED -i -E -f- $NAME/smr-verification.opam << 'EOF'
# s/^(maintainer|authors):.*/\1: "Anonymous author(s)"/
# s/^(homepage|bug-reports):.*/\1: "https:\/\/anonymous.authors"/
# /dev-repo/d
# s/^(synopsis):.*/\1: "SMR verification Coq development"/
# EOF

# replace iRC11 README with Compass README
# rm $NAME/README.md
# mv $NAME/README-COMPASS.md $NAME/README.md

# # Bundle the dependencies for the "archived" version.
# ( cd $NAME
#   git clone --quiet --depth 20 https://gitlab.mpi-sws.org/iris/stdpp
#   cd stdpp
#   git checkout --quiet ac02dbbd )
# ( cd $NAME
#   git clone --quiet --depth 20 https://gitlab.mpi-sws.org/iris/iris
#   cd iris
#   git checkout --quiet 72a4bd62 )
# ( cd $NAME
#   git clone --quiet --depth 20 https://gitlab.mpi-sws.org/iris/orc11
#   cd orc11
#   git checkout --quiet a1676613 )

# # Script for building the archive
# N=$(nproc)
# ( cd stdpp && make -j $N && make install )
# ( cd iris && ./make-package iris -j $N && ./make-package iris install )
# ( cd orc11 && make -j $N && make install )
# make -j $N


# exclude .git stuff and hide username
zip -r $NAME.zip $NAME \
    --exclude '*.git*' '*.vscode*' '*notes.md'

rm -rf $NAME
