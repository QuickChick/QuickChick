set -ev

opam init --yes --no-setup
eval $(opam config env)

opam repo add coq-released https://coq.inria.fr/opam/released

case $MODE in
  quickchick-plugin)
    opam pin add quickchick-plugin . --yes --verbose
    make -j4 tests
    ;;
  quickchick-tool)
    opam pin add quickchick-tool . --yes --verbose
    ;;
esac
