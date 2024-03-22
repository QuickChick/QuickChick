Testing Multifile Mutation
  $ quickChick -color > log 2>&1 || (cat log ; exit 1)
