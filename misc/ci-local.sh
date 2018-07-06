#!/bin/bash

# Runner installation
# -------------------
# apt-get update
# apt-get install curl autoconf automake
# curl -L https://packages.gitlab.com/install/repositories/runner/gitlab-runner/script.deb.sh | bash
# curl -fsSL https://download.docker.com/linux/debian/gpg | apt-key add -
# apt-key fingerprint 0EBFCD88
# echo "deb https://download.docker.com/linux/debian stretch stable" >> /etc/apt/sources.list
# apt-get update
# apt-get install gitlab-runner docker-ce
# gitlab-runner register
#   https://gitlab.inria.fr/
#   shell
# usermod -aG docker gitlab-runner

set -e
eval `opam config env`

ls -l .
wc -c install-sh || true
./configure --enable-local
make

while test $# -gt 0
do
    case "$1" in
        bench)
            bin/why3config --detect-provers
            make bench
            ;;
        ide)
            WHY3CONFIG="" xvfb-run bin/why3 ide --batch "" examples/logic/einstein.why
            ;;
        doc)
            make doc
            ;;
        nightly-bench)
            ls -l /usr/local/bin/
            file $(which cvc4-1.5)
            bin/why3config --detect-provers
            bench/ce-bench
            cat misc/bench-few-provers-why3-conf >> why3.conf
            examples/regtests.sh
            ;;
    esac
    shift
done
