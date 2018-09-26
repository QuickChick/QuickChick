#!/usr/bin/sudo /bin/bash
echo core >/proc/sys/kernel/core_pattern
echo performance | tee cd /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor

