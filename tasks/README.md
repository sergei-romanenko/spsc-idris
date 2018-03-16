# Tasks for SPSC in Idris

First, build SPSC executable by running
```
idris --build spsc_idris.ipkg
```

The tasks for SPSC are in files with the extension `.task`.

Go to this directory and, for each task `name`, run
```
../spsc_idris name
```
Then SPSC will read the file `name.task` and produce the files
`name.tree` (containig the process tree) and `name.res`
(containing the residual task).
