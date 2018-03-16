# A Small Positive Supercompiler in Idris

To run tests, execute
```
idris --testpkg spsc_idris.ipkg
```

To build the executable `spsc_idris`, execute
```
idris --build spsc_idris.ipkg
```

To run a sample task `name`, go to the subdirectory `tasks` and
execute
```
spsc_idris name
```

SPSC will read the file `name.task` and write the supercompiled
task into the file `name.res`. The process tree (= the graph of
configurations) will be written into the file `name.tree`.
