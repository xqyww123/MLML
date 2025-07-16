#!/bin/env python

from sqlitedict import SqliteDict
import sys
import csv
from collections import Counter

total = 0
success = 0
distr = Counter({})

COMMANDS = {'HAVE', 'END', 'NEXT', 'CONSIDER', 'RULE', 'UNFOLD', 'INTRO', 'APPLY', 'CRUSH',
            'CASE_SPLIT', 'INDUCT', 'OPEN_MODULE', 'CONFIG', 'DEFINE', 'LET', 'NOTATION'}

def distr_of_commands (script):
    all_commands = [line.split()[0] for line in script.splitlines() if line.strip() and line.split()]
    commands = [word for word in all_commands if word in COMMANDS]
    return Counter(commands)


decl = 0
end_only = 0
SH_only = 0
end_distr = Counter({})
have_distr = Counter({})
have_distr_origin = Counter({})
success_rate = Counter({})
total_lines = 0
refined_goals = 0

with SqliteDict('data/translation/results.db') as db:
    for k,v in db.items():
        file,line,cat = k.split(':')
        if cat == 'origin':
            decl += 1
            total += 1
        src, err, _, _ = v
        if cat == 'refined':
            lines = [x for x in src.strip().split('\n') if x.strip()]
            num_lines = len(lines)
            total_lines += num_lines
        if cat == 'refined':
            refined_goals += 1
            num_of_END = src.count('END')
            num_lines = src.strip().count('\n')
            if num_lines == 0 and src.strip().startswith('END'):
                end_only += 1
            end_distr[num_of_END] += 1
            num_of_HAVE = src.count('HAVE ')
            have_distr[num_of_HAVE] += 1
        if cat == 'isar-SH*':
            num_lines = src.strip().count('\n')
            if num_lines == 0 and src.strip().startswith('by (auto_sledgehammer'):
                SH_only += 1
        if cat == 'origin':
            num_of_HAVE = src.count('have ') + src.count('hence ')
            have_distr_origin[num_of_HAVE] += 1
            try:
                _, err2, _, _ = db[f"{file}:{line}:refined"]
                if not err2:
                    success_rate[num_of_HAVE] += 1
            except KeyError:
                pass
        if cat == 'refined':
            success += 1
            d = distr_of_commands(src)
            distr.update(d)
    #with open('result.csv', 'w', newline='') as f:
    #    w = csv.writer(f, delimiter=',', quotechar='\"', quoting=csv.QUOTE_MINIMAL)
    #    for k,v in db.items():
    #        match k.split(':'):
    #            case (file,line,cat):
    #                decl += 1
    #            case (file,line):
    #                if v[1]:
    #                    for t,s in v[1].items():
    #                        w.writerow([file,line,v[0],t,s])
    #                else:
    #                    w.writerow([file, line, v[0], v[1]])
    #                total += 1
    #                if v[1]:
    #                    success += 1
    #                    d = distr_of_commands(v[1]['refined'])
    #                    distrs[file, line] = d
    #                    distr.update(d)

print(f"{success} / {total} = {success / total}")
print(f"{decl} decls {total_lines} lines {refined_goals} goals")
print(f"{end_only} ({end_only / total * 100:0.2f}%) end-only")
print(f"{SH_only} ({SH_only / total * 100:0.2f}%) SH-only")

total_count = sum(distr.values())
percentage_distribution = {word: (count / total_count * 100) for word, count in distr.items()}
print(percentage_distribution)
aaa = [{'name': word, 'value': count / total_count * 100} for word, count in distr.items()]
print(aaa)


print('---------------END---------------')

total_end_only = sum(end_distr.values())
distr_end_only = {word: (count / total_end_only * 100) for word, count in end_distr.items()}
print(distr_end_only)

print('---------------HAVE---------------')

def norm(x):
    if x > 100:
        return 100
    else:
        return x

relative_have = {word: norm (count / have_distr_origin[word] * 100) if have_distr_origin[word] else 0 for word, count in success_rate.items()}

total_have = sum(have_distr.values())
distr_have = {word: (count / total_have * 100) for word, count in have_distr.items()}
print(distr_have)

print('---------------HAVE_ORIGIN---------------')

total_have_origin = sum(have_distr_origin.values())
distr_have_origin = {word: (count / total_have_origin * 100) for word, count in have_distr_origin.items()}
print(distr_have_origin)

print('---------------RELATIVE HAVE---------------')
print(relative_have)


# # Write distribution data to JSON files
# import json
# 
# # Write distr_have to JSON file
# with open('/tmp/distr_have.json', 'w') as f:
#     json.dump(distr_have, f, indent=2)
#     print("Saved distr_have to /tmp/distr_have.json")
# 
# # Write distr_have_origin to JSON file
# with open('/tmp/distr_have_origin.json', 'w') as f:
#     json.dump(distr_have_origin, f, indent=2)
#     print("Saved distr_have_origin to /tmp/distr_have_origin.json")
# 
# 
# # Read distribution data from JSON files
# try:
#     with open('/tmp/distr_have.json', 'r') as f:
#         distr_have = json.load(f)
#         print("Loaded distr_have from /tmp/distr_have.json")
# except FileNotFoundError:
#     print("Warning: /tmp/distr_have.json not found")
# 
# try:
#     with open('/tmp/distr_have_origin.json', 'r') as f:
#         distr_have_origin = json.load(f)
#         print("Loaded distr_have_origin from /tmp/distr_have_origin.json")
# except FileNotFoundError:
#     print("Warning: /tmp/distr_have_origin.json not found")


import matplotlib.pyplot as plt
from matplotlib.ticker import SymmetricalLogLocator
import matplotlib as mpl
from matplotlib.patches import ArrowStyle  # 导入 ArrowStyle 类

# Set the font to serif for the entire plot with larger font sizes
plt.rcParams['font.family'] = 'serif'
plt.rcParams['font.serif'] = ['Times New Roman']
plt.rcParams['font.size'] = 16  # Increase base font size
plt.rcParams['axes.labelsize'] = 18  # Larger font for axis labels
plt.rcParams['axes.titlesize'] = 22  # Larger font for titles
plt.rcParams['xtick.labelsize'] = 16  # Larger font for x-tick labels
plt.rcParams['ytick.labelsize'] = 16  # Larger font for y-tick labels
plt.rcParams['legend.fontsize'] = 16  # Larger font for legend

x0 = sorted(relative_have.keys())
y0 = [relative_have[k] for k in x0]

print(x0)
print(y0)

x1 = sorted(distr_have.keys())
y1 = [distr_have[k] for k in x1]

x2 = sorted(distr_have_origin.keys())
y2 = [distr_have_origin[k] for k in x2]

fig, ax1 = plt.subplots(figsize=(10, 6))  # Larger figure size for better visibility

# Create a second y-axis that shares the same x-axis
ax2 = ax1.twinx()

# Plot x0,y0 on the second axis (linear)
ax2.plot(x0, y0, linestyle='-', label='Success (linear)', color='red')
# Plot x1,y1 and x2,y2 on the first axis (logarithmic)
ax1.plot(x2, y2, linestyle=':', label='Isar (log)', color='blue')
ax1.plot(x1, y1, linestyle='--', label='MiniLang (log)', color='green')


# Add vertical dotted lines at x=0, x=1, and x=2
for x_pos in [0, 5, 10, 30]:
    ax1.axvline(x=x_pos, color='gray', linestyle=':', alpha=0.5)

for y_pos in [60,70,80]:
    ax2.axhline(y=y_pos, color='gray', linestyle=':', alpha=0.5)

# Add annotation with specific values at the first point
annotation_text = f"Isar: {y2[0]:.2f}%\nMiniLang: {y1[0]:.2f}%\nSuccess: {y0[0]:.2f}%"
ax2.annotate(annotation_text,
            xy=(0, 85),  # Position at the first point
            xytext=(10, -120),    # Offset text by 20 points
            textcoords='offset points',
            arrowprops=dict(
                arrowstyle='->',
                connectionstyle='angle,angleA=180,angleB=90,rad=0'
            ),
            fontsize=14)  # Larger font for annotation

# ax1.annotate(f"Isar: {y2[30]:.2f}%",
#             xy=(x2[30], y2[30]),
#             xytext=(-75, 40),
#             textcoords='offset points',
#             arrowprops=dict(arrowstyle='->'),
#             fontsize=16)

ax1.annotate(f"Isar: {y2[30]:.2f}%\nMiniLang: {y1[30]:.2f}%",
            xy=(28, y2[30]),
            xytext=(-180, 10),
            textcoords='offset points',
            arrowprops=dict(
                arrowstyle='->'
            ),
            fontsize=14)

# Set up the scales and ticks
ax1.set_xscale('symlog', linthresh=10)
ax1.set_yscale('log')  # Log scale for Isar and MiniLang
ax2.set_yscale('linear')  # Linear scale for Success Rate

# Set y-axis limits for both axes
ax1.set_ylim(0.01, 100)  # For log scale
ax2.set_ylim(0, 100)     # For linear scale

# Position the y-axis labels
ax1.yaxis.set_label_coords(-0.08, 0.8)

# Set up the x-ticks
linear_ticks = list(range(0, 10))  # 0, 1, 2, ..., 9
log_ticks = [10, 13, 16, 20, 30, 50, 80, 100, 200, 500]  # logarithmic region ticks
ax1.set_xticks(linear_ticks + log_ticks)

# Custom formatter to use string labels for 0-9 and regular formatting for larger numbers
def custom_formatter(x, pos):
    if x == 30:
        return '30 cmds'
    elif x < 10:
        return str(int(x))
    else:
        return str(int(x))

def format_y(y, pos):
    return str(y) + '%'

ax1.xaxis.set_major_formatter(plt.FuncFormatter(custom_formatter))
ax1.yaxis.set_major_formatter(plt.FuncFormatter(format_y))
ax2.yaxis.set_major_formatter(plt.FuncFormatter(format_y))

# Create a combined legend for both axes
lines1, labels1 = ax1.get_legend_handles_labels()
lines2, labels2 = ax2.get_legend_handles_labels()

ax1.grid(False)
ax2.grid(False)

# Place the legend directly on the plot, overlaying the curves
# 选择一个折线较少的区域放置图例
ax2.legend(lines1 + lines2, labels1 + labels2, 
           loc='upper right',  # 左上角位置，可以根据图形调整到合适的覆盖位置
           framealpha=0.9,    # 半透明背景
           fancybox=True)     # 圆角边框


# Add padding to the right side of the plot
plt.subplots_adjust(right=0.85)  # Adjust this value to add more space on the right

plt.show()
