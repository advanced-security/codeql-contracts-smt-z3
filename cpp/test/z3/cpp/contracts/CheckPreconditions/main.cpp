#include "assert.h"

void f1(int a, int b){
    /*@ requires @*/
    assert(a > b);
}

void m1(){
    int a = 0;
    int b = 0;

    f1(a, b); // NON-COMPLIANT
}

void m2(){
    int a = 1;
    int b = 10;

    f1(a, b); // NON-COMPLIANT
}

void m3(){
    int a = 10;
    int b = 1;

    f1(a, b); // COMPLIANT
}