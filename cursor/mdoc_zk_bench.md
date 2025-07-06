Unable to determine clock rate from sysctl: hw.cpufrequency: No such file or directory
This does not affect benchmark measurements, only the metadata output.
***WARNING*** Failed to set thread affinity. Estimated CPU frequency may be incorrect.
2025-07-06T11:54:00+03:00
Running ./circuits/mdoc/mdoc_zk_test
Run on (8 X 24 MHz CPU s)
CPU Caches:
  L1 Data 64 KiB
  L1 Instruction 128 KiB
  L2 Unified 4096 KiB (x8)
Load Average: 2.32, 2.48, 3.68
----------------------------------------------------------
Benchmark                Time             CPU   Iterations
----------------------------------------------------------
BM_MdocProver    481694458 ns    480629500 ns            2
BM_MdocVerifier  234873028 ns    234183000 ns            3
