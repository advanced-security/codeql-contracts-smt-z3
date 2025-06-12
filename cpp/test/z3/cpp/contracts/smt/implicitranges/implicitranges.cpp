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

void f2(){
    int i;
    A* c;
    A  d;

    *c->a = 100; // DNE in contract (contract is reference)
    *c->a = 109; // DNE in contract (contract is reference)
    
    c->d = 101;  // Exists in contract 
    c->d = 1011; // Exists in contract 

    *c->b->a = 102; // DNE in contract (contract is a reference)
    c->b->b->b->b->b = NULL; // Exists in contract (same type)
    
    *d.a = 103; // DNE in contract (contract is a reference)
    *d.b->a = 104; // DNE in contract (no reference)
    d.b->b->b->b->b = NULL; // Exists in contract (is a reference)

    i = 10; // DNE in contract 

    f1(i, c, d);
}