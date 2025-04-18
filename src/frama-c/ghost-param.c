/*@ ghost int g_function (int x){
 @   return x + 42;
 @ }
 @*/

//@ ghost int glob;

void function(int x) /*@ ghost (int parameter ) */ {
    //@ ghost int save_x = x;
    x++;
    //@ ghost glob = g_function(save_x + parameter);
    //@ assert glob == save_x + parameter + 42;
}

void caller(void) {
    function(3) /*@ ghost (4) */ ;
}

