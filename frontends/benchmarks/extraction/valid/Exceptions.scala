/* Test file */

import stainless.lang._

object ThrowCondition {

  def add_pos(a: BigInt, b: BigInt): BigInt = {
    a + b
  } throwing {
    e => true
  }
}
