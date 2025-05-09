import stainless.lang._
import stainless.collection._
import stainless.annotation._


def my_function(x: Int): Int = {
  var i = x

  (while (i > 0) {
    decreases(i)

    i -= 1
  }).invariant(i >= 0)

  i
}