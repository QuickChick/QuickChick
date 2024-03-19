Testing Multifile Mutation
  $ quickChick -color -ocamlbuild '-lib unix' > log || (cat log ; exit 1)
