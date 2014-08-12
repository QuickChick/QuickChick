QuickChick
==========

Description
 
  - QuickCheck for Coq using Extraction

Known to work with

  - Coq 8.4pl4
  - SSReflect 1.5
  - OCaml 4.01.0

Installation

  - make
  - make install doesn't work for now, you should use the plugin in the folder
    where it was built by make or copy all the files manually (you will need
    to copy at least src/quickChickLib.cmx and src/quickChickLib.o to
    coq-8.4pl4/user-contrib/QuickChick/ since for some reason coq_makefile
    forgets to do that)

Examples

  - Tests.v



