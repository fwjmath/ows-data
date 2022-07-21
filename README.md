# ows-data

Data and code of Odd Weird Search performed on yoyo@home

## Code

The source code (``wobt-smart.cpp``) is released under GPL 3.0. It contains some code in the public domain from [Thomas R. Nicely](https://www.trnicely.net). This code uses the [MPIR](https://www.mpir.org) library and the GCC-specific data type ``__int128``. By default, this code compiles into a standalone application, but it was also meant to be compiled as a [BOINC](https://boinc.berkeley.edu) application to be run on the volunteer computing project [yoyo@home](https://www.rechenkraft.net/yoyo/) by setting the macro ``__USING_BOINC``.

We note that the source code is for a search with a limit on the abundance of numbers. To remove this limit, either modify the code in the function ``search``, or putting the abundance bound in the input file as high as the upper bound of numbers.

And sorry for the badly written code that also lacks adequate comments...

## Application behavior

The application reads an input file indicating the part of factorization tree to search, then it searches for an [odd weird number](https://en.wikipedia.org/wiki/Weird_number). When the search is terminated, a result file is written, and the application terminates.

As an application designed for volunteer computing, after reaching a certain quantity of computation, the application will stop and write a checkpoint file, which is then sent back to the server. The checkpoint file has the same format as the input file. For more details, see

Fang, W., Beckert, U. Parallel Tree Search in Volunteer Computing: a Case Study. J Grid Computing 16, 647–662 (2018). [DOI](https://doi.org/10.1007/s10723-017-9411-5) (open access).

## Data format

### Input/checkpoint file

Here is an example of an input/checkpoint file

```
10000000000000000000000000000
1000000000000000000000
100000000000000
10
25310984
20000000611
37940809052
252390246
919117
1 1 3
2 1 5
3 1 7
6 1 17
13 1 43
37 1 163
87 1 457
154 1 907
2993 1 27397
```

Here is an explanation of the meaning of each line:

- Line 1: Upper bound of numbers that we check
- Line 2: Lower bound of numbers that we check
- Line 3: Upper bound of abundance of numbers that we check
- Line 4: Recursion depth (the number of distinct prime factors of the current number)
- Line 5: Number of odd weird candidates that are checked so far
- Line 6: Workpoint, a rough estimate of work already done in the current workunit, based on certain statistics on subset sum instances that are solved
- Line 7: Primepoint, a rough estimate of work already done in the current workunit, based on the number of primality tests executed up to now
- Line 8: Checksum, a quantity mixing various statistics to ensure correct computation by volunteers
- Line 9: The number of sections left in the current workunit
- The rest: Factorization of the current number. Each line corresponds to a prime, the first number is the index of the prime, the second its power, the third its value.

### Result file

A result file has roughly the same format as input/checkpoint files, with an extra line (the information line) at the end. There are several possibilities:

- "t": needed to recycle
- "c": completed, no recycle needed
- A message when an odd weird number is found.