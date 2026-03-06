import matplotlib.pyplot as plt
import matplotlib
import numpy as np
import csv, os

matplotlib.rcParams['font.family'] = 'Segoe UI'
matplotlib.rcParams['font.size'] = 11

csv_path = os.path.join(os.path.dirname(__file__), 'comparison-results.csv')
rows = []
with open(csv_path, newline='') as f:
    for r in csv.DictReader(f):
        rows.append(r)

devices       = [int(r['Device_ID']) for r in rows]
laaka_cpu     = [float(r['LAAKA_CPU_s']) for r in rows]
prop_cpu      = [float(r['Proposing_CPU_s']) for r in rows]
laaka_energy  = [float(r['LAAKA_Energy_J']) for r in rows]
prop_energy   = [float(r['Proposing_Energy_J']) for r in rows]

# Colour palette
C_LAAKA = '#E74C3C'   # red
C_PROP  = '#2ECC71'   # green
C_BG    = '#FAFAFA'
C_GRID  = '#E0E0E0'

x = np.arange(len(devices))
w = 0.38

out_dir = os.path.dirname(__file__)

# ─────────────────────────────────────────────────────────────
# Chart 1 — Per-Device CPU Time Comparison
# ─────────────────────────────────────────────────────────────
fig1, ax1 = plt.subplots(figsize=(14, 5.5))
fig1.patch.set_facecolor(C_BG)
ax1.set_facecolor(C_BG)

bars_l = ax1.bar(x - w/2, laaka_cpu, w, label='LAAKA', color=C_LAAKA,
                 edgecolor='white', linewidth=0.6, zorder=3)
bars_p = ax1.bar(x + w/2, prop_cpu,  w, label='Proposed Scheme', color=C_PROP,
                 edgecolor='white', linewidth=0.6, zorder=3)

ax1.set_xlabel('Device ID', fontweight='bold', fontsize=12)
ax1.set_ylabel('CPU Time (seconds)', fontweight='bold', fontsize=12)
ax1.set_title('Per-Device CPU Time: Proposed Scheme vs LAAKA',
              fontweight='bold', fontsize=14, pad=12)
ax1.set_xticks(x)
ax1.set_xticklabels([str(d) for d in devices], fontsize=9)
ax1.legend(frameon=True, fancybox=True, shadow=True, fontsize=11,
           loc='upper left')
ax1.grid(axis='y', color=C_GRID, linestyle='--', linewidth=0.7, zorder=0)
ax1.set_axisbelow(True)
ax1.spines[['top', 'right']].set_visible(False)

fig1.tight_layout()
fig1.savefig(os.path.join(out_dir, 'chart1_cpu_comparison.png'), dpi=200)
print('Chart 1 saved.')

# ─────────────────────────────────────────────────────────────
# Chart 2 — Per-Device Energy Comparison
# ─────────────────────────────────────────────────────────────
fig2, ax2 = plt.subplots(figsize=(14, 5.5))
fig2.patch.set_facecolor(C_BG)
ax2.set_facecolor(C_BG)

bars_l2 = ax2.bar(x - w/2, [e * 1000 for e in laaka_energy], w,
                  label='LAAKA', color='#3498DB',
                  edgecolor='white', linewidth=0.6, zorder=3)
bars_p2 = ax2.bar(x + w/2, [e * 1000 for e in prop_energy], w,
                  label='Proposed Scheme', color='#F39C12',
                  edgecolor='white', linewidth=0.6, zorder=3)

ax2.set_xlabel('Device ID', fontweight='bold', fontsize=12)
ax2.set_ylabel('Energy Consumption (mJ)', fontweight='bold', fontsize=12)
ax2.set_title('Per-Device Energy Consumption: Proposed Scheme vs LAAKA',
              fontweight='bold', fontsize=14, pad=12)
ax2.set_xticks(x)
ax2.set_xticklabels([str(d) for d in devices], fontsize=9)
ax2.legend(frameon=True, fancybox=True, shadow=True, fontsize=11,
           loc='upper left')
ax2.grid(axis='y', color=C_GRID, linestyle='--', linewidth=0.7, zorder=0)
ax2.set_axisbelow(True)
ax2.spines[['top', 'right']].set_visible(False)

fig2.tight_layout()
fig2.savefig(os.path.join(out_dir, 'chart2_energy_comparison.png'), dpi=200)
print('Chart 2 saved.')

# ─────────────────────────────────────────────────────────────
# Chart 3 — Average Summary (CPU + Energy side by side)
# ─────────────────────────────────────────────────────────────
avg_l_cpu = np.mean(laaka_cpu)
avg_p_cpu = np.mean(prop_cpu)
avg_l_e   = np.mean(laaka_energy) * 1000   # mJ
avg_p_e   = np.mean(prop_energy)  * 1000   # mJ

fig3, (ax3a, ax3b) = plt.subplots(1, 2, figsize=(10, 5.5))
fig3.patch.set_facecolor(C_BG)

# --- CPU sub-plot ---
ax3a.set_facecolor(C_BG)
b1 = ax3a.bar(['LAAKA', 'Proposed'], [avg_l_cpu, avg_p_cpu],
              color=[C_LAAKA, C_PROP], edgecolor='white', linewidth=1.2,
              width=0.55, zorder=3)
for bar, val in zip(b1, [avg_l_cpu, avg_p_cpu]):
    ax3a.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.008,
              f'{val:.4f} s', ha='center', va='bottom', fontweight='bold',
              fontsize=11)
cpu_imp = (avg_l_cpu - avg_p_cpu) / avg_l_cpu * 100
ax3a.set_title(f'Avg CPU Time\n(Proposed {cpu_imp:.1f}% lower)',
               fontweight='bold', fontsize=13, pad=10)
ax3a.set_ylabel('CPU Time (seconds)', fontweight='bold', fontsize=11)
ax3a.grid(axis='y', color=C_GRID, linestyle='--', linewidth=0.7, zorder=0)
ax3a.set_axisbelow(True)
ax3a.spines[['top', 'right']].set_visible(False)
ax3a.set_ylim(0, max(avg_l_cpu, avg_p_cpu) * 1.25)

# --- Energy sub-plot ---
ax3b.set_facecolor(C_BG)
b2 = ax3b.bar(['LAAKA', 'Proposed'], [avg_l_e, avg_p_e],
              color=['#3498DB', '#F39C12'], edgecolor='white', linewidth=1.2,
              width=0.55, zorder=3)
for bar, val in zip(b2, [avg_l_e, avg_p_e]):
    ax3b.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.4,
              f'{val:.2f} mJ', ha='center', va='bottom', fontweight='bold',
              fontsize=11)
e_imp = (avg_l_e - avg_p_e) / avg_l_e * 100
ax3b.set_title(f'Avg Energy Consumption\n(Proposed {e_imp:.1f}% lower)',
               fontweight='bold', fontsize=13, pad=10)
ax3b.set_ylabel('Energy (mJ)', fontweight='bold', fontsize=11)
ax3b.grid(axis='y', color=C_GRID, linestyle='--', linewidth=0.7, zorder=0)
ax3b.set_axisbelow(True)
ax3b.spines[['top', 'right']].set_visible(False)
ax3b.set_ylim(0, max(avg_l_e, avg_p_e) * 1.25)

fig3.suptitle('Overall Performance: Proposed Scheme vs LAAKA',
              fontweight='bold', fontsize=15, y=1.02)
fig3.tight_layout()
fig3.savefig(os.path.join(out_dir, 'chart3_average_summary.png'), dpi=200,
             bbox_inches='tight')
print('Chart 3 saved.')

print('\nAll 3 charts generated successfully!')
