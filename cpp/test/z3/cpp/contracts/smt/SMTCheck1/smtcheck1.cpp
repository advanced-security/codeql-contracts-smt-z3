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


void f3(A *a){
    /*@ requires @*/
    assert(a == NULL);
}


void t1(){
    int *a;
    
    if(a == NULL){
        f1(a, 3);
        f2(a);
    }

}


void t2(){
    int *a;

    
    if(a != NULL){
        f1(a, 3);
        f2(a);
    }
}


void t3(){
    A *b;

    if(b==NULL){
        f3(b);
    }
}

void t4(){
    A *b;

    if(b!=NULL){
        f3(b);
    }
}