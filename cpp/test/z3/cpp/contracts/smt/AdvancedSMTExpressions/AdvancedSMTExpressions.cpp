#include "assert.h"
#include <cstddef>

class A {
public:
    int *a;
    int d;
    A *b;
    int operator==(A x)
    {
        return 0;
    }
};

void f1(int i, A* a, A &b){

    /*@ requires @*/
    assert(a);

    /*@ requires @*/
    assert(a->a);

    /*@ requires @*/
    assert(a->d > 0);

    /*@ requires @*/
    assert(a->d);

    /*@ requires @*/
    assert(b.a);
        
    /*@ requires @*/
    assert(a->b->a);

    /*@ requires @*/
    assert(b.b->a);

    /*@ requires @*/
    assert(b.b->b->b->b->b);

    /*@ requires @*/
    assert(a->b->b->b->b->b);
}

