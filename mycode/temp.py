for t in table_bound:
    min_upbound = 10000
    max_lower_bound = 0
    for tmp_elem in table_outline_elem_lst:
        if tmp_elem['y0'] > t[1][1]:
            if tmp_elem['y0'] < min_upbound:
                min_upbound = tmp_elem['y0']  # 更新最小上界

        if tmp_elem['y0'] < t[0][1]:
            if tmp_elem['y0'] > max_lower_bound:
                max_lower_bound = tmp_elem['y0']  # 更新最大下界
    bounds_x = {}

    # 下边这两个用来补 缺失的x-seg
    lower_bounds = []
    upper_bounds = []
    for tmp_elem in table_outline_elem_lst:
        if same(tmp_elem['y0'], min_upbound):
            bounds_x[tmp_elem['x0']] = 'left'
            bounds_x[tmp_elem['x1']] = 'right'
            lower_bounds.append(tmp_elem)
        if same(tmp_elem['y0'], max_lower_bound):
            upper_bounds.append(tmp_elem)

    for k in bounds_x:
        tmp_elem = {
            'x0': k,
            'x1': k,
            'y0': max_lower_bound,
            'y1': min_upbound,
            'isLine': 'y'
        }

        # 使用文本帮助合并表格
for text_line in text_cols:
    last_tid = 0
    merge = None
    for i in range(1, len(my_tables)):
        y0 = text_line['box'][0][1]
        top_y = my_tables[last_tid][-1][0]
        bottom_y = my_tables[i][0][0]
        if y0 > top_y and y0 < bottom_y:
            # 处于两个table间，合并两个table
            merge = [last_tid, i]
            break
        last_tid = i
    if merge:
        for line in my_tables[merge[1]]:
            my_tables[merge[0]].append(line)
        del my_tables[merge[1]]

print len(my_tables)
# 移除 太短的线
for idx in range(len(t) - 1, -1, -1):
    length = t[idx][1][-1] - t[idx][1][0]
    if len(t[idx][1]) == 1:
        del t[idx]

last_x = t[-1][1][0]
t[-1][1])):
tmp_elem = {
    'x0': last_x,
    'x1': t[-1][1][ii],
    'y0': y,
    'y1': y,
    'isLine': 'x'
}
last_x = t[-1][1][ii]
table_outline_elem_lst.append(tmp_elem)

for idx, t in enumerate(my_tables):
    last_line = t[0]
for i in range(1, len(t)):
    extend_point = []
for new_p in last_line[1]:
    start = t[i][1][0]
end = t[i][1][-1]
if new_p < start - 1 or new_p > end + 1:
    extend_point.append(new_p)
t[i][1].extend(extend_point)
t[i][1].sort()
####

y_and_sx = sorted(y_and_its_xs.iteritems(), key=lambda x: x[0])
for l in y_and_sx:
    last_p = l[1][0]
pairs = []
for i in range(1, len(l[1])):
    if abs(last_p - l[1][i]) <= 15:  # 12 is the size of a char
        pairs.insert(0, [i - 1, i])
        last_p = l[1][i]
    for prex, curr in pairs:
        del l[1][curr]
    l[1].sort()
    l[1][0] = 52
    add_segs(l[1], l[0], table_outline_elem_lst)
    # 合并过短的线段，对齐 表格中的点位置