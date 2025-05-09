import stainless.lang._
import stainless.collection._
import stainless.annotation._

def int_max(x: Int, y: Int): Int = {
    if (x > y) x else 0
}.ensuring(res => res >= x && res >= y)
