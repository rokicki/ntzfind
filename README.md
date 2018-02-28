# ntzfind
Changes so far:

* Faster search (about 1.6X; more for asymetric searches)

* Added support for widths > 10

* Reduced memory consumption (only 19GB needed for width 11 searches)

* Table generation much faster (more than 5x for large tables)

* Table generation dynamic (as needed) rather than up-front

* Rule parsing integrated; no need for separate python script

* Added randomized search order; are you feeling lucky?

* Asymmetric searches now twice as fast because mirror images not searched

* Various bugs fixed from original sources

I compile with g++ -std=c++11 -O3 -march=native -o ntzfind ntzfind.cpp; make
sure to enable C++11 support in your compiler.
