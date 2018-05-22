/* Test file */

import stainless.lang._

case class MyException() extends Exception

object ThrowCondition {

  def add_pos(a: BigInt, b: BigInt): BigInt = {
    if(a < 0 || b < 0) throw MyException()
    else a + b
  } throwing {
    _ => true
  }
}
