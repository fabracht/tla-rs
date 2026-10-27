---- MODULE NNU_EEE_defA ----
EXTENDS Naturals, NNU_EEE_defABase
K == INSTANCE NNU_EEE_defB WITH y <- w * 2
Read1 == K!Read2
====
