IF(MSVC_INTEL)
  PROJECT(wolfssl C ASM_MASM)
ELSEIF(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|amd64")
  PROJECT(wolfssl C ASM)
ELSE()
  PROJECT(wolfssl C)
ENDIF()

IF(CMAKE_SIZEOF_VOID_P MATCHES 8)
IF(MSVC_INTEL)
  SET(WOLFSSL_INTELASM ON)
  SET(WOLFSSL_X86_64_BUILD 1)
  SET(HAVE_INTEL_RDSEED 1)
  SET(HAVE_INTEL_RDRAND 1)
ELSEIF(CMAKE_SYSTEM_PROCESSOR MATCHES "x86_64|amd64")
  SET(WOLFSSL_X86_64_BUILD 1)
  IF(CMAKE_C_COMPILER_ID MATCHES GNU  AND CMAKE_C_COMPILER_VERSION VERSION_LESS 4.9)
    MESSAGE_ONCE(NO_INTEL_ASSEMBLY "Disable Intel assembly for WolfSSL - compiler is too old")
  ELSE()
    IF(WITH_MSAN)
      MESSAGE_ONCE(MSAN_CANT_HANDLE_IT "Disable Intel assembly for WolfSSL - MSAN can't handle it")
    ELSE()
      MY_CHECK_C_COMPILER_FLAG(-maes)
      MY_CHECK_C_COMPILER_FLAG(-msse4)
      MY_CHECK_C_COMPILER_FLAG(-mpclmul)
      IF(have_C__maes AND have_C__msse4 AND have_C__mpclmul)
        SET(WOLFSSL_INTELASM ON)
      ENDIF()
    ENDIF()
    MY_CHECK_C_COMPILER_FLAG(-mrdrnd)
    MY_CHECK_C_COMPILER_FLAG(-mrdseed)
    IF(have_C__mrdrnd)
      SET(HAVE_INTEL_RDRAND ON)
    ENDIF()
    IF(have_C__mrdseed)
      SET(HAVE_INTEL_RDSEED ON)
    ENDIF()
  ENDIF()
ENDIF()
ENDIF()

SET(WOLFSSL_SRCDIR ${CMAKE_CURRENT_SOURCE_DIR}/wolfssl/src)
SET(WOLFCRYPT_SRCDIR ${CMAKE_CURRENT_SOURCE_DIR}/wolfssl/wolfcrypt/src)
ADD_DEFINITIONS(${SSL_DEFINES})
ADD_DEFINITIONS(-DWOLFSSL_LIB -DBUILDING_WOLFSSL)
INCLUDE_DIRECTORIES(BEFORE ${CMAKE_CURRENT_SOURCE_DIR}/wolfssl)
INCLUDE_DIRECTORIES(${SSL_INCLUDE_DIRS})

add_library(wolfssl STATIC
${WOLFSSL_SRCDIR}/crl.c
${WOLFSSL_SRCDIR}/internal.c
${WOLFSSL_SRCDIR}/keys.c
${WOLFSSL_SRCDIR}/tls.c
${WOLFSSL_SRCDIR}/wolfio.c
${WOLFSSL_SRCDIR}/ocsp.c
${WOLFSSL_SRCDIR}/ssl.c
${WOLFSSL_SRCDIR}/tls13.c
${WOLFCRYPT_SRCDIR}/aes.c
${WOLFCRYPT_SRCDIR}/arc4.c
${WOLFCRYPT_SRCDIR}/asn.c
${WOLFCRYPT_SRCDIR}/coding.c
${WOLFCRYPT_SRCDIR}/des3.c
${WOLFCRYPT_SRCDIR}/dh.c
${WOLFCRYPT_SRCDIR}/dsa.c
${WOLFCRYPT_SRCDIR}/ecc.c
${WOLFCRYPT_SRCDIR}/error.c
${WOLFCRYPT_SRCDIR}/hmac.c
${WOLFCRYPT_SRCDIR}/logging.c
${WOLFCRYPT_SRCDIR}/md4.c
${WOLFCRYPT_SRCDIR}/md5.c
${WOLFCRYPT_SRCDIR}/memory.c
${WOLFCRYPT_SRCDIR}/pkcs12.c
${WOLFCRYPT_SRCDIR}/pwdbased.c
${WOLFCRYPT_SRCDIR}/random.c
${WOLFCRYPT_SRCDIR}/rsa.c
${WOLFCRYPT_SRCDIR}/sha.c
${WOLFCRYPT_SRCDIR}/sha256.c
${WOLFCRYPT_SRCDIR}/sha512.c
${WOLFCRYPT_SRCDIR}/poly1305.c
${WOLFCRYPT_SRCDIR}/chacha.c
${WOLFCRYPT_SRCDIR}/chacha20_poly1305.c
${WOLFCRYPT_SRCDIR}/wc_port.c
${WOLFCRYPT_SRCDIR}/wc_encrypt.c
${WOLFCRYPT_SRCDIR}/hash.c
${WOLFCRYPT_SRCDIR}/wolfmath.c
${WOLFCRYPT_SRCDIR}/kdf.c
${WOLFCRYPT_SRCDIR}/sp_int.c
)

# Optimizations, assembly
if(WOLFSSL_X86_64_BUILD)
  target_sources(wolfssl PRIVATE ${WOLFCRYPT_SRCDIR}/cpuid.c)
  if(MSVC_INTEL)
    set(WOLFSSL_AESNI 1)
    target_sources(wolfssl PRIVATE
      ${WOLFCRYPT_SRCDIR}/aes_asm.asm
      ${WOLFCRYPT_SRCDIR}/aes_gcm_asm.asm)
    if(CMAKE_C_COMPILER_ID MATCHES Clang)
      target_compile_options(wolfssl PRIVATE  $<$<COMPILE_LANGUAGE:C>:-maes -msse4.2 -mpclmul -mrdrnd -mrdseed> )
    endif()
  elseif(WOLFSSL_INTELASM)
    set(WOLFSSL_AESNI 1)
    set(USE_INTEL_SPEEDUP 1)
    target_sources(wolfssl PRIVATE
      ${WOLFCRYPT_SRCDIR}/aes_asm.S
      ${WOLFCRYPT_SRCDIR}/aes_gcm_asm.S
      ${WOLFCRYPT_SRCDIR}/chacha_asm.S
      ${WOLFCRYPT_SRCDIR}/poly1305_asm.S
      ${WOLFCRYPT_SRCDIR}/sha512_asm.S
      ${WOLFCRYPT_SRCDIR}/sha256_asm.S)
    target_compile_options(wolfssl PRIVATE -maes -msse4.2 -mpclmul)
    # Workaround 5.5.4 bug (user_settings.h not included into aes_asm.S)
    set_property(SOURCE ${WOLFCRYPT_SRCDIR}/aes_asm.S APPEND PROPERTY COMPILE_OPTIONS "-DWOLFSSL_X86_64_BUILD")
  endif()
endif()

# Silence some warnings
if(MSVC)
  # truncation warnings
  target_compile_options(wolfssl PRIVATE $<$<COMPILE_LANGUAGE:C>:/wd4244>)
  if(CMAKE_C_COMPILER_ID MATCHES Clang)
    target_compile_options(wolfssl PRIVATE $<$<COMPILE_LANGUAGE:C>:-Wno-incompatible-function-pointer-types>)
  endif()
endif()

CONFIGURE_FILE(user_settings.h.in user_settings.h)

