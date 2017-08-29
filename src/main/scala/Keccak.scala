/**
 * Scala implementation of some of the FIPS202 and SP800-185 functions.
 * Based on work done by the Keccak, Keyak and Ketje teams, namely, 
 * Guido Bertoni, Joan Daemen, Michael Peeters, Gilles Van Assche and 
 * Ronny Van Keer. 
 *
 * For more inforation about these projects please refer to the
 * following websites:
 * http://keccak.noekeon.org
 * http://keyak.noekeon.org
 * http://ketje.noekeon.org
 *
 * The Python implementation of FIPS202 by Renaud Bauvin 
 * was also used as reference. As was the Javascript implementation of
 * Keccak related functions by Chen, Yi-Cyuan (located at 
 * http://github.com/emn178/js-sh3). The golang.org/x/crypto/sha3 library
 * provided additional insight.
 *
 * Implementation in Scala by Aaron Scott, hereby denoted as 
 * "the implementer"
 * To the extent possible under law, the implementor has waved all
 * copyright and related or neighboring rights to the source code
 * in this file.
 * http://creativecommons.org/publicdomain/zero/1.0/
 */
import scala.annotation.switch
import scala.annotation.tailrec
import scala.util.Try

package com.github.ascottqqq.scalakeccak {

  object Keccak {
    private val BitsInAByte = 8
    private val BitsInALong = 64
    /** bitwise right circular shift */
    private def rol64(a: Long, n: Int): Long = {
      (a >>> (BitsInALong - (n % BitsInALong))) | (a << (n % BitsInALong))
    }
  
    /** main Keccak[1600] rounds done on 64 bit lanes */
    private def keccakF1600OnLanes(lanes: Vector[Vector[Long]]): Vector[Vector[Long]] = {

      @tailrec
      def keccakRound(lanes: Vector[Vector[Long]], rc: List[Long], round: Int = 0): 
        Vector[Vector[Long]] = {

        val R = Vector(
          Vector( 0, 28,  1, 27, 62),
          Vector(44, 20,  6, 36, 55),
          Vector(43,  3, 25, 10, 39),
          Vector(21, 45,  8, 15, 41),
          Vector(14, 61, 18, 56,  2)
        )

        (round: @switch) match {
          case 24 => lanes
          case _ => {
            def theta (result: Vector[Vector[Long]]): Vector[Vector[Long]] = {
              val c = result.map(x => x(0) ^ x(1) ^ x(2) ^ x(3) ^ x(4))
              val d = c.zipWithIndex.map {
                case (element, x) => c((x+4)%5) ^ rol64(c((x+1)%5), 1) // +4 == -1 % 5
              }
              result.zipWithIndex.map { 
                case (row, x) => row.map (
                  value => value ^ d(x)
                )
              }
            }
            var result = theta(lanes)

            @tailrec
            def rhoAndPi(lanes: Vector[Vector[Long]], current: Long, 
              x: Int = 0, y: Int = 2, t: Int = 0): Vector[Vector[Long]] = {
              (t: @switch) match {
                case 24 => lanes
                case _ => {
                  rhoAndPi(x = y, y = (2*x+3*y)%5, 
                  lanes = lanes.updated(x, lanes(x).updated(y, rol64(current, 
                    R(x)(y)))),
                  current = lanes(x)(y), t = t+1)
                }
              }
            }
            result = rhoAndPi(lanes = result, current = result(1)(0))

            def chi(result: Vector[Vector[Long]]): Vector[Vector[Long]] = {
              result.zipWithIndex.map{
                case(row, x) => row.zipWithIndex.map {
                  case (value, y) => value ^ ((~result((x+1)%5)(y)) & (result((x+2)%5))(y))
                }
              }
            }
            result = chi(result)

            def iota(result: Vector[Vector[Long]], rc: List[Long]): (Vector[Vector[Long]], 
              List[Long]) = {

              (result.updated(0, result(0).updated(0, result(0)(0) ^ rc.head)), rc.tail)
            }

            val (resultI, rcI) = iota(result, rc)
            keccakRound(resultI, rcI, round + 1)
          }
        }
      }

      // round constants
      val Rc=List(0x0000000000000001L, 0x0000000000008082L, 0x800000000000808AL,
        0x8000000080008000L, 0x000000000000808BL, 0x0000000080000001L, 
        0x8000000080008081L, 0x8000000000008009L, 0x000000000000008AL,
        0x0000000000000088L, 0x0000000080008009L, 0x000000008000000AL,
        0x000000008000808BL, 0x800000000000008BL, 0x8000000000008089L,
        0x8000000000008003L, 0x8000000000008002L, 0x8000000000000080L,
        0x000000000000800AL, 0x800000008000000AL, 0x8000000080008081L,
        0x8000000000008080L, 0x0000000080000001L, 0x8000000080008008L)

      keccakRound(lanes, Rc)
    }

    /** byte vector to lane */
    private def load64(b: Vector[Byte]) : Long = {
      b.zipWithIndex.map{case (element, i) => (element & 0xFFL) << (BitsInAByte * i)}.sum
    }

    /** lane to byte vector */
    private def store64(a: Long): List[Byte] = {
      List.tabulate(8)(i => (a >>> (BitsInAByte * i)).toByte)
    }

    /** Keccak F1600 on vector of bytes */
    private def keccakF1600(state: Vector[Byte]): Vector[Byte] = {
      var lanes = Vector(
        Vector(0L, 0L, 0L, 0L, 0L),
        Vector(0L, 0L, 0L, 0L, 0L),
        Vector(0L, 0L, 0L, 0L, 0L), 
        Vector(0L, 0L, 0L, 0L, 0L),
        Vector(0L, 0L, 0L, 0L, 0L)
      );      
      lanes = lanes.zipWithIndex.map {
        case (row, x) => row.zipWithIndex.map {
          case (element, y) => {
            val offset = 8*(x+5*y)
            load64(state.slice(offset, offset+8))
          }
        }
      }

      lanes = keccakF1600OnLanes(lanes)
      var result = Vector.fill(200)(0.toByte)
   
      for (x <- 0 until 5; y <- 0 until 5) {
        var offset = 8*(x+5*y)
        result = result.patch(offset, store64(lanes(x)(y)), 8)
      }
      result
    }

    /** keccakf1600 function on byte Vector with padding and squeezing */
    private def keccak(rate: Int, capacity: Int, inputBytes: Vector[Byte], 
      delimitedSuffix: Byte, outputByteLen: Int): Try[Vector[Byte]] = {
  
      require((rate + capacity) == 1600, "rate plus capacity must always equal 1600")
      require((rate % 8 == 0), "rate must be evenly divisble by 8, ie rate must be in bytes")

      var outputBytes = Vector[Byte]()
      var state = Array.fill(200)(0.toByte)
      var rateInBytes = rate/BitsInAByte
      var blockSize = 0
      var inputOffset = 0

      // Absorbing phase
      while(inputOffset < inputBytes.length) { 
        blockSize = math.min(inputBytes.length-inputOffset, rateInBytes)
        for(i <- 0 until blockSize) {
          state(i) = (state(i) ^ inputBytes(i+inputOffset)).toByte
        }
        inputOffset = inputOffset + blockSize
        if (blockSize == rateInBytes) {
          state = keccakF1600(state.toVector).toArray
          blockSize = 0
        }
      }
      // pad last block
   
      state(blockSize) = (state(blockSize)^delimitedSuffix).toByte

      if(((delimitedSuffix & 0x80) != 0) && (blockSize == (rateInBytes-1))) {
        state = keccakF1600(state.toVector).toArray
      }
      state(rateInBytes-1) = (state(rateInBytes-1)^(0x80)).toByte
      state = keccakF1600(state.toVector).toArray
      var loopCounter = outputByteLen

      // squeeze
      while(loopCounter > 0) {
        blockSize = math.min(loopCounter, rateInBytes)
        outputBytes = outputBytes ++ state.slice(0, blockSize).toVector
        loopCounter = loopCounter - blockSize
        if (loopCounter > 0) {
          state = keccakF1600(state.toVector).toArray
        }
      }
      Try(outputBytes)   
    }

    private val ShakeSuffix = 0x1F.toByte
    private val Sha3Suffix = 0x06.toByte
  
    def shake128(inputBytes: Vector[Byte], outputLength: Int): Try[Vector[Byte]] = {
      keccak(1344, 256, inputBytes, ShakeSuffix, outputLength/BitsInAByte)
    }

    def shake256(inputBytes: Vector[Byte], outputLength: Int): Try[Vector[Byte]] = {
      keccak(1088, 512, inputBytes, ShakeSuffix, outputLength/BitsInAByte)
    }

    def sha3_224(inputBytes: Vector[Byte]): Try[Vector[Byte]] = {
      keccak(1152, 448, inputBytes, Sha3Suffix, 224/BitsInAByte)
    }

    def sha3_256(inputBytes: Vector[Byte]): Try[Vector[Byte]] = {
      keccak(1088, 512, inputBytes, Sha3Suffix, 256/BitsInAByte)
    }

    def sha3_384(inputBytes: Vector[Byte]): Try[Vector[Byte]] = {
      keccak(832, 768, inputBytes, Sha3Suffix, 384/BitsInAByte)
    }

    def sha3_512(inputBytes: Vector[Byte]): Try[Vector[Byte]] = {
      keccak(576, 1024, inputBytes, Sha3Suffix, 512/BitsInAByte)
    }

    // NIST.SP.800-185

    private val Kmac = Vector(0x4b.toByte, 0x4d.toByte, 0x41.toByte, 0x43.toByte)
    private val Keccak256Rate = 168
    private val Keccak512Rate = 136
    private val CShakeSuffix = 0x04.toByte

    @tailrec
    private def calculateByteLength(value: Int, n: Int = 0): Byte = {
      (n, value) match {
        case (n, v) if ((value == 0) || (n >= 255)) => n.toByte
        case (n, v) => calculateByteLength(value >>> BitsInAByte, n + 1)
      }
    }

    def leftEncode(value: Int): Vector[Byte] = {
      val n = calculateByteLength(value)
      if (n == 0) {
        Vector(1.toByte, 0.toByte)
      } 
      else {
        n +: Vector.tabulate(n)(i => (value >>> (BitsInAByte * i)).toByte).reverse
      }
    }

    def rightEncode(value: Int): Vector[Byte] = {
      val n = calculateByteLength(value)
      if (n == 0) {
        Vector(1.toByte, 0.toByte) 
      }
      else {
        Vector.tabulate(n)(i => (value >>> (BitsInAByte * i)).toByte).reverse :+ n
      }
    }

    private def encodeString(s: Vector[Byte]): Vector[Byte] = {
      leftEncode(s.length * BitsInAByte) ++ s
    }  

    private def bytePad(x: Vector[Byte], w: Int): Vector[Byte] = {
      var z = leftEncode(w) ++ x
      if (z.length % w == 0) Vector[Byte]() else (1 to w - z.length % w).foldLeft(z) {
        (accumulator, i) => accumulator :+ 0x00.toByte
      }
    }
    
    def cShake128(x: Vector[Byte], l: Int, n: Vector[Byte], s: Vector[Byte]): 
      Try[Vector[Byte]] = {

      if(n.length == 0 && s.length == 0) {
        shake128(x, l)
      }
      else {
        keccak(1344, 256, bytePad(encodeString(n) ++ encodeString(s), 
          Keccak256Rate) ++ x, CShakeSuffix, l/BitsInAByte)
      }
    }

    def cShake256(x: Vector[Byte], l: Int, n: Vector[Byte], s: Vector[Byte]): 
      Try[Vector[Byte]] = {

      if(n.length == 0 && s.length == 0) {
        shake256(x, l)
      }
      else {
        keccak(1088, 512, bytePad(encodeString(n) ++ encodeString(s), 
          Keccak512Rate) ++ x, CShakeSuffix, l/BitsInAByte)
      } 
    }

    def kmac128(k: Vector[Byte], x: Vector[Byte], l: Int, s: Vector[Byte]): 
      Try[Vector[Byte]] = {
    
      val newX = bytePad(encodeString(k), Keccak256Rate) ++ x ++ rightEncode(l)
      cShake128(newX, l, Kmac, s)
    }
  
    def kmac256(k: Vector[Byte], x: Vector[Byte], l: Int, s: Vector[Byte]): 
      Try[Vector[Byte]] = {

      val newX = bytePad(encodeString(k), Keccak512Rate) ++ x ++ rightEncode(l)
      cShake256(newX, l, Kmac, s)
    }
  }
}