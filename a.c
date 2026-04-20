#include "Primitives.h"

void simple(int n) {
 int x = 0;
 return whilef_0(x,n);
 }

void whilef_0(int x,int n) {
 bool v_14 = lt(x,n);
 if (v_14) {
    {
   int v_12 = 1;
   x=plus(x,v_12);
   };
   return whilef_0(x,n);
   } else {
   return ;
   };
 }

