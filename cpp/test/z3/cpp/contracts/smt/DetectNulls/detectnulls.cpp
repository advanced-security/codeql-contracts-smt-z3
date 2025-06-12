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
}

void f4(A *a){
    /*@ requires @*/
    assert(a);
}

void f5(A *a){
    /*@ requires @*/
    assert(a != NULL);
}

// tricky case because they may pass the object and not 
// the field
void f6(A &b){
    /*@ requires @*/
    assert(b.a);

    /*@ requires @*/
    assert(b.a != NULL);
}


void t1(){
    int *a;
    int b;

    f1(a, b);

    if(a != NULL){
        f1(a,b);
    }else{
        f1(a,b);
    }

    if(a == NULL){
        f1(a,b);
    }
}

void t2(){
    int b;
    int *a = &b;

    f1(a, b);

    if(a != NULL){
        f1(a,b);
    }else{
        f1(a,b);
    }

    if(a == NULL){
        f1(a,b);
    }
}

void t3(){
    int b;
    int *a = &b;

    f1(a, b);

    if(a != NULL){
        f1(a,b);
    }else{
        f1(a,b);
    }

    f1(a,b);
}


void t4(){
    int b;
    int *a;

    f1(a, b);

    if(a != NULL){
        f1(a,b);
    }else{
        f1(a,b);
    }

    f1(a,b);
}

