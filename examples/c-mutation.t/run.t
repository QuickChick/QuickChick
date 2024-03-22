Testing Multifile Mutation
  $ quickChick -color -ocamlbuild '-lib unix' > log 2>&1 || (cat log ; exit 1)
