package export

// Generated by 'goexports crypto/rsa'. Do not edit!

import "crypto/rsa"

// CryptoRsa contains exported symbols from crypto/rsa
var CryptoRsa = &map[string]interface{}{
	"CRTValue":                  new(rsa.CRTValue),
	"DecryptOAEP":               rsa.DecryptOAEP,
	"DecryptPKCS1v15":           rsa.DecryptPKCS1v15,
	"DecryptPKCS1v15SessionKey": rsa.DecryptPKCS1v15SessionKey,
	"EncryptOAEP":               rsa.EncryptOAEP,
	"EncryptPKCS1v15":           rsa.EncryptPKCS1v15,
	"ErrDecryption":             rsa.ErrDecryption,
	"ErrMessageTooLong":         rsa.ErrMessageTooLong,
	"ErrVerification":           rsa.ErrVerification,
	"GenerateKey":               rsa.GenerateKey,
	"GenerateMultiPrimeKey":     rsa.GenerateMultiPrimeKey,
	"OAEPOptions":               new(rsa.OAEPOptions),
	"PKCS1v15DecryptOptions":    new(rsa.PKCS1v15DecryptOptions),
	"PSSOptions":                new(rsa.PSSOptions),
	"PSSSaltLengthAuto":         rsa.PSSSaltLengthAuto,
	"PSSSaltLengthEqualsHash":   rsa.PSSSaltLengthEqualsHash,
	"PrecomputedValues":         new(rsa.PrecomputedValues),
	"PrivateKey":                new(rsa.PrivateKey),
	"PublicKey":                 new(rsa.PublicKey),
	"SignPKCS1v15":              rsa.SignPKCS1v15,
	"SignPSS":                   rsa.SignPSS,
	"VerifyPKCS1v15":            rsa.VerifyPKCS1v15,
	"VerifyPSS":                 rsa.VerifyPSS,
}