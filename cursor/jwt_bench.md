Unable to determine clock rate from sysctl: hw.cpufrequency: No such file or directory
This does not affect benchmark measurements, only the metadata output.
***WARNING*** Failed to set thread affinity. Estimated CPU frequency may be incorrect.
2025-07-06T11:52:56+03:00
Running ./circuits/jwt/jwt_test
Run on (8 X 24 MHz CPU s)
CPU Caches:
  L1 Data 64 KiB
  L1 Instruction 128 KiB
  L2 Unified 4096 KiB (x8)
Load Average: 2.53, 2.53, 3.79
[INFO][+ 3343.068 ms] Compiled circuit: mdoc revocation list
[INFO][+    0.053 ms]  depth: 26 wires: 717611 in: 16006 out:64 use:589859 ovh:127752 t:2149994 cse:982759 notn:1841510
[INFO][+   78.740 ms] Fill done
[INFO][+    0.197 ms] ZK Commit start
[INFO][+   65.354 ms] ZK Commitment done
[INFO][+  325.871 ms] ZK sumcheck done
[INFO][+    2.190 ms] ZK constraints done
[INFO][+   23.602 ms] Prover Done: flag
[INFO][+ 2256.596 ms] Compiled circuit: mdoc revocation list
[INFO][+    0.048 ms]  depth: 26 wires: 717611 in: 16006 out:64 use:589859 ovh:127752 t:2149994 cse:982759 notn:1841510
[INFO][+   77.475 ms] Fill done
[INFO][+    0.159 ms] ZK Commit start
[INFO][+   64.942 ms] ZK Commitment done
[INFO][+  328.537 ms] ZK sumcheck done
[INFO][+    2.301 ms] ZK constraints done
[INFO][+   25.415 ms] Prover Done: flag
[INFO][+    1.083 ms] ZK Commit start
[INFO][+   64.907 ms] ZK Commitment done
[INFO][+  326.302 ms] ZK sumcheck done
[INFO][+    2.514 ms] ZK constraints done
[INFO][+   24.407 ms] Prover Done: flag
---------------------------------------------------------
Benchmark               Time             CPU   Iterations
---------------------------------------------------------
BM_JwtZKProver  420689833 ns    418693500 ns            2
