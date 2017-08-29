A scala implementaton of some of the Keccak functions.
The scala test testing framework was used.

result is a Try

example of usage:

import com.github.ascottqqq.scalakeccak.Keccak

object Main extends App {

  var key = Vector.tabulate(32)(x => (x + 0x40).toByte)
  var message = Vector.tabulate(4)(x => x.toByte)

  println(Keccak.kmac256(key, message, 512, 
    "My Tagged Application".toCharArray.map(_.toByte).toVector))
}