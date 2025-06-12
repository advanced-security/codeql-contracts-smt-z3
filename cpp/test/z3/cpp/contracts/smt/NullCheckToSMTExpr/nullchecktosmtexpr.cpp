#include "assert.h"
#include <cstddef>

class A {
public:
    int *a;
    int d;
    int operator==(A x)
    {
        return 0;
    }
};

void f1(int *a, int b){
    /*@ requires @*/
    assert(a);

    /*@ requires @*/
    assert(a && b > 0);

}

void f2(int *a){
    /*@ requires @*/
    assert(a != NULL);

    /*@ requires @*/
    assert(a == NULL);

    /*@ requires @*/
    assert(!a);
}

void f4(A *a){
    /*@ requires @*/
    assert(a);
}

void f5(A *a){
    /*@ requires @*/
    assert(a != NULL);

    /*@ requires @*/
    assert(a == NULL);

    /*@ requires @*/
    assert(!a);
}

// tricky case because they may pass the object and not 
// the field
void f6(A &b){
    /*@ requires @*/
    assert(b.a);

    /*@ requires @*/
    assert(b.a != NULL);

    /*@ requires @*/
    assert(b.a == NULL);

    /*@ requires @*/
    assert(!b.a);

}

