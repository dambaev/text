# Text

STATE: work in progress.

This library's goal is to be an analogue to 'text' library in Haskell for ATS.

This library depends on:
1. Bytestring library (https://github.com/dambaev/ats-bytestring);
2. libunistring.

Bytestring is being used for runtime representation of multibyte strings and libunistring is being used for working with multibyte codepoints.

For now, this library only supports for NFD normalization for the function, that must support normalization (encoding from Bytestring and equality checks).

# Example

```ats

fn test0(): void = {
  val bs = $BS.pack "привет world"
  val () = assertloc( length bs = 18)

  val t = $T.decode_utf8 bs
  val () = assertloc( length t = 12)

  val () = free t
}

```

You can find more examples in TEST directory
