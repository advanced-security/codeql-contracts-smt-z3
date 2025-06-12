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

void f1(){
    int *a;
    int b;
    /*@ requires @*/
    assert(a);

    /*@ requires @*/
    assert(a && b > 0);

}

void f2(){
    int *a;
    /*@ requires @*/
    assert(*a > 1);
}

void f3(){
    int *a;
    /*@ requires @*/
    assert(a != NULL);
}

void f4(){
    A *a = new A();
    /*@ requires @*/
    assert(a);
}

void f5(){
    A *a = new A();
    /*@ requires @*/
    assert(a != NULL);
}

void f6(){
    A b;
    /*@ requires @*/
    assert(b.a);

    /*@ requires @*/
    assert(b.a != NULL);
}

void f7(){
    A a;

    if(a.a != NULL){
        /*@ requires @*/
        assert(a.a);

        /*@ requires @*/
        assert(a.a != NULL);
    }
}

void f8(){
    int a = 100;
    int *b = &a;

    /*@ requires @*/
    assert(*b < 100);
}

void f9(){
    A b;
    A *c = new A();

    /*@ requires @*/
    assert(*(b.a) > 0);

    /*@ requires @*/
    assert(*(c->a) > 0);

    /*@ requires @*/
    assert(c->d > 0);

    /*@ requires @*/
    assert(b.d > 0);
}

void f10(){
    A b;
    A c;
    int d;

    /*@ requires @*/
    assert(b == c && *(c.a) > 0);

    /*@ requires @*/
    assert(b == c && d > 0);
}

void f11(){
    A b;
    A c;

    /*@ requires @*/
    assert(b == c && c == b);

    /*@ requires @*/
    assert(b == c);
}

void f12(){
    char a;
    int d;

    /*@ requires @*/
    assert(d == 0 && a == 'a');

    /*@ requires @*/
    assert(a == 'a');

}


void f13(){
    int *a;

    if(a != NULL){
        /*@ requires @*/
        assert(a);

        /*@ requires @*/
        assert(a != NULL);
    }
}