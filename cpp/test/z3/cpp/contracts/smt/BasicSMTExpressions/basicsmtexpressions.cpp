#include "assert.h"
#include <cstddef>


void f1(int i){

    /*@ requires @*/
    assert(i > 0);

    /*@ requires @*/
    assert(i >= 0);

    /*@ requires @*/
    assert(i < 0);

    /*@ requires @*/
    assert(i <= 0);

    /*@ requires @*/
    assert(i == 0);

    /*@ requires @*/
    assert(!(i > 0));

    /*@ requires @*/
    assert(i + 1 > 0);

    /*@ requires @*/
    assert(i - 1 < 0);
        
    /*@ requires @*/
    assert(i + 1 <= 0);
}

void f2(int i){

    /*@ requires @*/
    assert(i == 0 && i == 0);

    /*@ requires @*/
    assert(!(i > 0) && i < 10);

    /*@ requires @*/
    assert(i + 1 > 0 && i > 0);

    /*@ requires @*/
    assert(i - 1 < 0 && i > 0);
        
    /*@ requires @*/
    assert(i + 1 <= 0 || i >= 100);

    /*@ requires @*/
    assert((i + 1 <= 0) || (i >= 100));

    /*@ requires @*/
    assert(i + 1 <= 0 && i >= 10);

}
