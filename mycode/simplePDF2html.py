#!/usr/bin/python
#coding=utf-8

import os
import re
import gc
import sys
import copy
import time
import json
#import numpy as np

import operator # 为了排序
import turtle # 为了可视化显示检测到的布局
from collections import OrderedDict

from pdfminer.converter import PDFPageAggregator
from pdfminer.pdfparser import PDFParser
from pdfminer.pdfdocument import PDFDocument
from pdfminer.pdfpage import PDFPage
from pdfminer.pdfpage import PDFTextExtractionNotAllowed
from pdfminer.pdfinterp import PDFResourceManager
from pdfminer.pdfinterp import PDFPageInterpreter
from pdfminer.layout import *


reload(sys)
sys.setdefaultencoding('utf8') #设置默认编码
# sys.getdefaultencoding() #'ascii'
UCC = 0

base_struct = {
  "Total": 1,
  "ElapsedTime": 1,
  "Hits": [
    {
      "Id": "4282431",
      "Source": {
        "Key": None,
        "Title": "宜华健康：关于签署购买资产框架协议的公告",
        "Paragraphs": [],
        "Pages": [],
        "SubTitles": [],
        "PublishDate": "2016-12-30T00:00:00",
        "StockCode": "000150",
        "StockTicker": "宜华健康",
        "Url": "https://stock.tianyancha.com/announcement/",
        "Industry": "",
        "ParentIndustry": "",
        "Province": "浙江省",
        "RelevantLaws": [
          {
            "LawId": 0,
            "LawTitle": "《中华人民共和国公司法》"
          },
          {
            "LawId": 0,
            "LawTitle": "《广告业发展“十三五”规划》"
          }
        ],
        "Href": "/Home/DisclosureDetail?key=DsHIVSygwhgqacIphu2iYw==&market=1",
        "TotalPage": 0,
        "FileType": 1
      },
      "Highlight": {
        "Content": [
          "【预览】 ..."
        ],
        "Title": []
      },
      "Cat": None,
      "Cmt": None,
      "FavTime": "0001-01-01T00:00:00"
    }
  ],
  "Aggregations": [],
  "Token": None,
  "Message": None
}

def same(x,y):
    return abs(x-y) < 1.1

def split_lines(slash_elem_lst):
    sv_line = []
    segs = []
    if len(slash_elem_lst) > 0:

        for item in sorted(slash_elem_lst.iteritems(), key=lambda x: x[0][0]):
            sv_line.append(item[0])

        last_l = sv_line[0]
        for i in range(len(sv_line)):
            if sv_line[i][0] <  last_l[1] + 12: #未超过一个字符
                last_l = [last_l[0], max(last_l[1], sv_line[i][1])]
            else:
                segs.append(last_l)
                last_l = sv_line[i]
        segs.append(last_l)
    return segs


def merge_same_line(raw_lines) :
    x_lines = {}
    y_lines = {}
    lines = []
    for p in raw_lines:
        if p[0][1] == p[1][1]:   # 水平线
            if p[0][1] not in x_lines:
                x_lines[p[0][1]] = []
            x_lines[p[0][1]].extend([p[0][0],p[1][0]])
        if p[0][0] == p[1][0]: # 垂直线
            if p[0][0] not in y_lines:
                y_lines[p[0][0]] = []
            y_lines[p[0][0]].extend([p[0][1], p[1][1]])

    for k in x_lines:
        x_lines[k].sort()

        start_p = x_lines[k][0]
        last_p = start_p
        for i in range(1, len(x_lines[k])):
            curr = x_lines[k][i]
            if curr - last_p > 2:#紧邻
                lines.append(([start_p,k],[last_p,k]))
                start_p = curr
            last_p = curr

    for k in y_lines:
        y_lines[k].sort()
        lines.append(([k, y_lines[k][0]],
                      [k, y_lines[k][-1]]))
    return lines

# a and sub is order list
def is_sub_list(a, sub):
    s = 0
    try:
         while  s <len(a) and not same(a[s], sub[0]):
            s +=1
    except Exception,ex:
        pass
    if len(a) - s < len(sub):
        return False
    flag = True
    for i,v in enumerate(sub):
        if not same(a[s+i], sub[i]):
            flag = False
            break
    return flag







def sheet_head_split(t):
    #第一行和第二行 分段数不同

    if len(t) >= 2:
        l1 = t[-1][1]
        l2 = t[-2][1]
        start = 0 # 记录最后一次相等的点
        # 检查表头点的一致性
        for i in range(len(l1)):
            if l1[i] not in l2:
                dis = abs(l1[-1] - l1[0])
                best_p = None
                for p in l2:
                    if abs(p - l1[i]) < dis:
                        dis = abs(p - l1[i])
                        best_p = p
                if best_p is None:
                    return None
                elif best_p not in l1:
                    l1.append(best_p)

        if len(l1) != len(l2):
            for i in range(min(len(l1),len(l2))):
                if not same(l1[i], l2[i]):
                    break
                start = i  # record the same location
            y = min(t[-1][0]-20, (t[-1][0]+t[-2][0])/2)
            return [y, l1, start]
    return None


def merge_ys(t):
    last_idx = 0
    remove_idx = []
    for curr in range(1,len(t)):
        if abs(t[last_idx][0] - t[curr][0])<10: # 小于一个字符
            if len(t[last_idx]) == 3 and t[last_idx][2] =='text': #优先保留文本计算出的行
                remove_idx.append(curr)
            else:
                remove_idx.append(last_idx)
                last_idx = curr
        else:
            last_idx = curr
    for idx in remove_idx[::-1]:
        del t[idx]



def uniform_segs(t):
    last_line = t[0]
    left = last_line[1][0]
    right = last_line[1][-1]
    for idx in range(1, len(t)):  # every line
        line = t[idx]
        left = min(left, line[1][0])
        right = max(right, line[1][-1])
        for i, new_p in enumerate(line[1]):  # 每一个点
            for p in last_line[1]:
                if same(new_p, p):
                    t[idx][1][i] = p
                    break
        last_line = line
    # 确保线到达左右边界
    for idx in range(len(t)):
        if same(left, t[idx][1][0]):
            t[idx][1][0] = left #保证
        else:
            t[idx][1].insert(0, left)
        if same(right, t[idx][1][-1]):
            t[idx][1][-1] = right
        else:
            t[idx][1].append(right)


def add_segs(xs,y,table_outline_elem_lst):
    last_x = xs[0]
    for i in range(len(xs)):
        tmp_elem = {
            'x0': last_x,
            'x1': xs[i],
            'y0': y,
            'y1': y,
            'isLine': 'x'
        }
        last_x = xs[i]
        table_outline_elem_lst.append(tmp_elem)

def in_range(value , bottom, up):
    b = min( bottom, up)
    u = max( bottom, up)
    if value > b and  value< u:
        return True
    return False



def get_corners(line, flag):
    text = ""
    char_list = []
    for char in line:
        if isinstance(char, LTChar):
            if u''!=char.get_text().strip():
                char_list.append(char)
            text += char.get_text()

    #if flag:
    #    print text


    if len(char_list) > 0:
        return (char_list[0].x0, line.y0),(char_list[-1].x1,line.y1),False

    return (line.x0,line.y0) , (line.x1,line.y1),True

def same_row(line, new_line):
    bottom = line['box'][0][1]
    up = line['box'][1][1]

    #有一个点在 range中，就认为是相同的线
    if new_line['box'][0][1]  > bottom-1 and new_line['box'][0][1]  < up+1:
        return True
    if new_line['box'][1][1]  > bottom-1 and new_line['box'][1][1]  < up+1:
        return  True

    return  False

def same_cols(line, new_line):
    left = line[0][0]
    right = line[1][0]

    if new_line[0][0]  > left-1 and new_line[0][0]  < right+1:
        return True
    if new_line[1][0]  > left-1 and new_line[1][0]  < right+1:
        return  True

    return  False

def parse_page_to_lines(layout):
    page_lines = []

    for x in layout:
        if (isinstance(x, LTTextBoxHorizontal)):

            for miner_line in x:
                if (isinstance(miner_line, LTTextLineHorizontal)):
                    corner_ld, corner_ru, empty = get_corners(miner_line, False)
                    #if empty:
                    #    continue
                    new_line = { 'box': [[corner_ld[0],corner_ld[1]], [corner_ru[0],corner_ru[1]]], \
                                 'text_lines': [(corner_ld, corner_ru)]}

                    for line in page_lines:
                        if same_row(line, new_line):
                            #合并的line, 更新数据
                            # p0.x, p0.y
                            line['box'][0][0] = min(line['box'][0][0], new_line['box'][0][0])
                            line['box'][0][1] = min(line['box'][0][1], new_line['box'][0][1])
                            # p1.x, p1.y
                            line['box'][1][0] = max(line['box'][1][0], new_line['box'][1][0])
                            line['box'][1][1] = max(line['box'][1][1], new_line['box'][1][1])
                            # find corresponding cols
                            for idx,l in enumerate(line['text_lines']):
                                if same_cols(l,new_line['box']):
                                    #merge two text line ,防止文字多的行，被选为最大列
                                    line['text_lines'][idx] =[
                                        (min(line['text_lines'][idx][0][0] , new_line['box'][0][0]),min(line['text_lines'][idx][0][1] , new_line['box'][0][1])),\
                                        (max(line['text_lines'][idx][1][0], new_line['box'][1][0]),max(line['text_lines'][idx][1][1], new_line['box'][1][1]))
                                    ]
                                    new_line = None
                                    break
                            if new_line:
                                line['text_lines'].append(new_line['text_lines'][0])
                                get_corners(miner_line, True)
                                new_line = None
                            break


                    #没找到可以合并的line
                    if new_line:
                        page_lines.append(new_line)
                    if len(page_lines) == 11:
                        pass
    len_last_line = 1
    tables = []
    text_cols = []

    left_bound = 10000
    right_bound = 0

    for l in page_lines:
        print l['box'][1][1] - l['box'][0][1], len(l['text_lines']),  l['box'][1][0] - l['box'][0][0]
        if left_bound > l['box'][0][0]:
            left_bound = l['box'][0][0]
        if right_bound < l['box'][1][0]:
            right_bound = l['box'][1][0]

        if len(l['text_lines']) > 1:
            text_cols.append(l)
            if len_last_line > 1:
                tables[-1].append(l)
            else:
                tables.append([l])
        len_last_line = len(l['text_lines'])
    #到这里就可以画出所有的水平线了
    print len(tables)
    table_bound = []
    for t in tables:
        box = t[0]['box']
        for i in range(1,len(t)):
            row = t[i]['box']
            box[0][0] = min(box[0][0], row[0][0])
            box[0][1] = min(box[0][1], row[0][1])
            box[1][0] = max(box[1][0], row[1][0])
            box[1][1] = max(box[1][1], row[1][1])
        table_bound.append(box)

    # merge cols
    return page_lines, text_cols

    """
    bounder_lines = []
    for t in tables:
        last_row = t[0]['box']
        up_y = last_row[1][1] + 6
        bounder_lines.append([[left_bound, up_y], [right_bound, up_y]])  # 做个max的限制
        for i in range(1,len(t)):
            y = (last_row[0][1] + t[i]['box'][1][1])/2
            bounder_lines.append([[left_bound,y],[right_bound,y]])
            last_row = t[i]['box']
        bottom_y =  t[-1]['box'][0][1]-6
        bounder_lines.append([[left_bound, bottom_y], [right_bound, bottom_y]])


    col_tables =[]

    for t in tables:
    #计算 列box
        max_cols = 0
        row_id = 0

        for idx,l in enumerate(t):
            if len(l['text_lines']) > max_cols:
                max_cols = len(l['text_lines'])
                row_id = idx
        table_col = []
        #记录列数最大的列中的元素box
        for tline in sorted(t[row_id]['text_lines'],key = lambda x:x[0][0]):
            table_col.append({ 'box': [[tline[0][0],tline[0][1]],[tline[1][0],tline[1][1]]], 'text_cols': [tline]})

        for idx, l in enumerate(t):
            if idx == row_id:
                continue
            for tl in l['text_lines']:
                same_cols_id = []
                for k,col in enumerate(table_col):
                    if same_cols(col['box'], tl):
                        same_cols_id.append(k)
                if len(same_cols_id) == 0:
                    pass # no common col 考虑添加新的列， 可以考虑将table_col 初始化时的排序去掉。
                elif len(same_cols_id) == 1:
                    cid = same_cols_id[0]
                    table_col[cid]['box'] = [
                        (min(table_col[cid]['box'][0][0], tl[0][0]), min(table_col[cid]['box'][0][1], tl[0][1])),
                        (max(table_col[cid]['box'][1][0], tl[1][0]), max(table_col[cid]['box'][1][1], tl[1][1]))
                    ]
                    table_col[cid]['text_cols'].append(tl)
                else:
                    # 该文本存在 cospan, 不做col合并
                    pass
        last_box = table_col[0]
        for i in range(1,len(table_col)):
            y0 = min(table_col[i]['box'][0][1], last_box['box'][0][1])
            y1 = max(table_col[i]['box'][1][1], last_box['box'][1][1])
            x0 = (table_col[i]['box'][0][0]+last_box['box'][1][0])/2
            x1 = x0
            last_box = table_col[i]
            bounder_lines.append([[x0,max(y0-6,0)],[x1,y1+6]])#做个max的限制
        col_tables.append(table_col)

    """



class PDF2HTML(object):
    def __init__(self, pdf_path, html_path, password="", codec='utf-8', bias_param=[1.5, 2]):
        self.pdf_path = pdf_path
        self.html_path = html_path
        self.codec = codec
        self.bias_param = bias_param
        self.reader = open(pdf_path, 'rb')
        self.writer = open(html_path, 'w')  # 'a'
        self.json_path = os.path.join("/Users/kevinhuang/svn/pdfweb/pdfweb/resources/data/", os.path.basename(html_path).replace('html','json'))
        self.debug_log = open('debug.log', 'a')
        self.password = password
        self.device = None
        self.indent = '  '
        self.level = 0
        self.outlines = None
        self.outlines_dict = None

        self.debug_mode_on = False #True
        self.pages = []
        self.page_html = ""
        self.catalog_separator = ""
        self.subtitles = []
        self.curr_anchor_id = 1
        # http://webdesign.about.com/od/styleproperties/p/blspfontweight.htm
        self.fontweight_dict = {
            self.chinese_str('ABCDEE+黑体'): 'bold',
            self.chinese_str('ABCDEE+宋体'): 'normal'
        }
        self.endmark_list = [
            self.chinese_str('：'),
            self.chinese_str(':'),
            self.chinese_str('。'),
            self.chinese_str('？'),
            self.chinese_str('?'),
            self.chinese_str('！'),
            self.chinese_str('!'),
            self.chinese_str('；')
        ]
    # print "init"
    def __enter__(self):
        # print "enter"
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        # print "exits"
        return
    def __del__(self):
        # print "deleted"
        self.reader.close()
        self.writer.close()
        self.debug_log.close()
        if self.device:
            self.device.close()
        sys._clear_type_cache()
        gc.collect()

    def write(self, content, body=False):
        if body:
            self.page_html += content
        self.writer.write(self.level * self.indent + str(content).encode('utf-8') + '\n')


    def is_catalog(self, content ):

        catalog_base_word = {u'第': '', u'章': '', u'节': '',
                             u'一': 1, u'二': 2, u'三': 3, u'四': 4, u'五': 5,
                             u'六': 6, u'七': 7, u'八': 8, u'九': 9, u'十': 10
                             }

        candidate_space = content.split(' ')[0].decode('utf-8')
        if len(candidate_space) >= 3: # 第一章
            is_space_title = True
            for c in candidate_space:
                if c not in catalog_base_word:
                    is_space_title = False
                    break
            if is_space_title is True:
                #if len(self.subtitles) == 0:
                self.catalog_separator = " "
                self.subtitles.append({'stName': content,
                                       'anchorId': "p{0}".format(self.curr_anchor_id), 'sub': []})
                return True

        candidate_dayton = content.split('、')[0].decode('utf-8')
        if len(candidate_dayton) >= 1: # 一
            is_dayton_title = True
            for c in candidate_dayton:
                if c not in catalog_base_word:
                    is_dayton_title = False
                    break
            if is_dayton_title is True:
                if self.catalog_separator is " ":
                    self.subtitles[-1]['sub'].append({'stName': content,
                                                      'anchorId': "p{0}".format(self.curr_anchor_id)})
                else:
                    self.subtitles.append({'stName': content, 'anchorId': "p{0}".format(self.curr_anchor_id)})
                return True
        return False

    def write2(self, text, align, font_size, weight, indent, page_id=-1):

        content = text
        is_catalog = False
        if u'..........' in content:
            content_list = content.split(' ')
            catalog_list = []
            for item in content_list:
                catalog_list.append(item)
                catalog_list.append('&nbsp;')
                if item.isdigit():
                    catalog_list.append('<br>')
            content = ''.join(catalog_list)
        else:
            is_catalog = self.is_catalog(content) # 需要用字号 排除一下干扰

        is_page_number = text.isdigit() and int(text) > 0

        if is_catalog or weight is not 'normal': # font_size > 12 or
            content = '<b>{0}</b>'.format(content)
        content = '{0}{1}'.format(int(indent)*'&emsp;', content)

        if is_catalog is True:
            content = '<p id="p{0}" align="{1}">{2}</p>'.format(self.curr_anchor_id, align, content)
            self.curr_anchor_id += 1
            if self.curr_anchor_id == 8:
                pass
            print self.curr_anchor_id
        else:
            content = '<p align="{0}">{1}</p>'.format(align, content)

        self.write(content, not is_page_number)

    def debug_write(self, content):
        self.debug_log.write(str(content).encode('utf-8') + '\n')

    def chinese_str(self, content, codec='utf-8'):
        return u'{0}'.format(content).encode('gbk')

    def get_last_char(self, content):
        length = len(content)
        return content[length - 1:]

    def sort_dict_by_val(self, dictdata, reverse=True):
        return sorted(dictdata.items(), key=operator.itemgetter(1), reverse=reverse)

    def convert(self, bias_param=None):
        pass

    def writeHTML(self):
        pass
    def writeHead(self):
        pass
    def writeBody(self):
        pass


class simplePDF2HTML(PDF2HTML):

    # 转换格式主函数
    def convert(self, bias_param=None):
        if bias_param:
            self.bias_param = bias_param
        print "initializing the parser setting..."
        self.simpleParse()

        print "writing to the HTML file..."
        self.writeHTML()
        pass

    def simpleParse(self):
        # 创建一个PDF文档解析器对象
        self.parser = PDFParser(self.reader)
        # 创建一个PDF文档对象存储文档结构
        self.document = PDFDocument(self.parser, self.password)
        # 检查文件是否允许文本提取
        if not self.document.is_extractable:
            raise PDFTextExtractionNotAllowed

        # 试试看能否直接提取目录
        try:
            raw_outlines = None#self.document.get_outlines()
        except Exception, e:
            raw_outlines = None

        self.outline_levels = []
        self.outlines_dict = {}
        self.outline_titles = []
        self.drawn_outline = []
        self.outline_ids = []
        if raw_outlines:  # pdfpage #pdfdocument #pdftypes
            print "there are outlines included"
            for (level, title, dest, a, se) in raw_outlines:
                """
                print level
                print title
                print dest
                """
                # print dest[0].resolve()
                # print dest[0].resolve()['Resources']['ExtGState']['GS0'].objid
                # outline_objid = dest[0].resolve()['Resources']['ExtGState']['GS0'].objid
                if dest and 'ExtGState' in dest[0].resolve()['Resources']:
                    outline_objid = 0
                    for key in dest[0].resolve()['Resources']['ExtGState'].keys():
                        if key[:2] == 'GS':
                            outline_objid = dest[0].resolve()['Resources']['ExtGState'][key].objid
                            break
                else:
                    continue
                self.outline_levels.append(level)
                self.outlines_dict[title] = outline_objid
                self.outline_titles.append(title)
                self.drawn_outline.append(False)
                self.outline_ids.append(outline_objid)
                # print outline_objid
                # print dest[0].resolve()['Parent']
                # print dest[0].resolve()['StructParents']
                # raw_input()
                # print self.document._cached_objs
                # for title in self.outlines_dict:
                #     print title
                #     print self.outlines_dict[title]
        # 创建一个PDF资源管理器对象来存储共享资源
        self.rsrcmgr = PDFResourceManager()
        # 创建一个PDF设备对象
        self.laparams = LAParams()
        # 创建一个PDF页面聚合对象
        self.device = PDFPageAggregator(self.rsrcmgr, laparams=self.laparams)
        # 创建一个PDF解析器对象
        self.interpreter = PDFPageInterpreter(self.rsrcmgr, self.device)
        # 字符转换规则
        self.replace = re.compile(r'\s+')

    def writeHTML(self):
        # print "write?"
        self.write('<!DOCTYPE html>')
        self.write('<html>')
        self.level += 1
        # write header
        self.writeHead()
        self.writeBody()
        self.level -= 1
        self.write('</html>')

    def writeHead(self):
        self.write('<head>')
        self.level += 1
        self.write('<meta http-equiv="Content-Type" content="text/html; charset=%s">\n' % self.codec)
        self.write('<title>PDF格式转HTML</title>')
        '''
        self.write('<style>')
        self.level += 1
        self.write('p {')
        self.level += 1
        self.write('text-indent: 2.0em;')
        self.level -= 1
        self.write('};')
        self.level -= 1
        self.write('</style>')
        '''
        self.level -= 1
        self.write('</head>')

    def writeBody(self):
        self.write('<body>')
        self.level += 1
        # 循环遍历列表，每次处理一个page的内容
        page_idx = 1
        ended = False
        prev_text = None
        prev_size = None
        prev_weight = None
        prev_indent = None
        prev_align = None
        prev_length = None
        for idx,page in enumerate(PDFPage.create_pages(self.document)):
            page_idx = idx + 1
            #if page_idx < 94:
            #    continue
            #if page_idx > 6:
            #    break
            if idx > 0:
                #record last page
                #print "#%s#"%self.page_html[-5:]
                self.pages.append({'PageNo': idx, 'PageContent': self.page_html})
                self.page_html = ""
            print "processing page {0}".format(page_idx)
            # print page
            # print page.resources
            # print page.resources['ExtGState']['GS0'].objid
            page_objid = 0
            if 'ExtGState' in page.resources:  # and 'GS0' in page.resources['ExtGState']:
                page_objid = 0
                for key in page.resources['ExtGState'].keys():
                    if key[:2] == 'GS':
                        page_objid = page.resources['ExtGState'][key].objid
                        break
            self.write('<div id="{0}">'.format(page_objid), True)
            self.level += 1
            # print page_objid
            # if page_objid in self.outlines.keys():
            # 是一个目录项的对应页
            # print self.outlines[page_objid]
            # print self.outlines[page_objid]
            # print "page " + str(page_idx)
            self.interpreter.process_page(page)
            # 接受该页面的LTPage对象
            layout = self.device.get_result()
            #self.show_page_layout(layout)
            page_lines,text_cols = parse_page_to_lines(layout)
            col_lines = []
            #self.show_page_layout_lines(layout, col_lines)
            # 页面左右上下
            page_xrange = (layout.x0, layout.x1)
            page_yrange = (layout.y0, layout.y1)
            # print page_xrange, page_yrange
            content_xrange, indent_list, fontsize_list = self.get_indent_info(layout, page_xrange)
            if len(indent_list) == 0 or len(fontsize_list) == 0:  # 空白页
                print idx, "empty"
                continue
            content_width = content_xrange[1] - content_xrange[0]
            major_indents, map_indents, major_size = self.get_conclude(indent_list, fontsize_list)
            typical_length = content_width / major_size
            # get table contents in advance

            table_points_list, bias, table_divider_list = self.get_tables(layout,text_cols)
            table_frames = []
            in_table = []  # true / false
            table_drawn = []  # true / false
            for i in range(len(table_points_list)):
                table_points = table_points_list[i]
                tmp_frame = self.get_table_frame(table_points, bias, table_divider_list[i])
                if tmp_frame.grids:
                    table_frames.append(tmp_frame)
                    table_drawn.append(False)
                    # print tmp_frame.grids
            # print table_frames
            # 去除嵌套结构以及页码的外框
            i = len(table_frames) - 1
            while i > 0:
                j = i - 1
                while j >= 0:
                    # print table_frames[i].grids
                    # print table_frames[j].grids
                    # print table_frames[i].included_in_table(table_frames[j])
                    # print table_frames[j].included_in_table(table_frames[i])
                    if table_frames[i].included_in_table(table_frames[j]):
                        table_frames.pop(j)
                        table_drawn.pop(j)
                        break
                    elif table_frames[j].included_in_table(table_frames[i]):
                        table_frames.pop(i)
                        table_drawn.pop(i)
                        break
                    j -= 1
                i -= 1
            # 将属于表格内的内容填进表格内
            for x in layout:
                if (isinstance(x, LTTextBoxHorizontal)):
                    # in_table.append(-1) # -1 for not included in any table; else: the table frame's index
                    table_idx = -1
                    for line in x:
                        if (isinstance(line, LTTextLineHorizontal)):
                            for i in range(len(table_frames)):
                                # table_frames[i]

                                corner1,corner2,empty = get_corners(line, False)

                                if table_frames[i].is_in_range(corner1) and table_frames[i].is_in_range(corner2):
                                    table_idx = i
                                    break
                            if table_idx != -1:
                                break
                    in_table.append(table_idx)
                    #print "#%s"%table_idx
                    if table_idx != -1:
                        for line in x:
                            if (isinstance(line, LTTextLineHorizontal)):
                                # table_frames[table_idx]
                                parts = {}  # location: text
                                for char in line:
                                    if isinstance(char, LTChar):
                                        text_line = re.sub(self.replace, '', char.get_text())
                                        if len(text_line):
                                            corner1 = (char.x0, char.y1)
                                            corner2 = (char.x1, char.y0)
                                            location = table_frames[table_idx].locate(corner2)
                                            # print location, text_line
                                            # raw_input()
                                            if (location):
                                                if location in parts.keys():
                                                    parts[location] += text_line
                                                else:
                                                    parts[location] = text_line
                                for location in parts.keys():
                                    table_frames[table_idx].add_data(location, parts[location])
                                    if table_frames[table_idx].font[location[0]][location[1]] == None:
                                        table_frames[table_idx].font[location[0]][location[1]] = int(line.y1 - line.y0)
            # print in_table

            for i in range(len(table_frames)):
                max_col = 1
                for line in table_frames[i].data:
                    if len(line) > max_col:
                        max_col = len(line)
                if max_col <= 1:
                    # not a real table, dirty data
                    for j in range(len(in_table)):
                        if in_table[j] == i:
                            in_table[j] = -1

            #### 预处理找出目录内容 ###
            # step 1: 先找出每项对应的目录项的坐标和位置
            in_outline = []
            outline_lines = []  # contents: [[y0, y1]], length: outline_lines
            for x in layout:
                if (isinstance(x, LTTextBoxHorizontal)):
                    outline_text = x.get_text()
                    tmp_outline_idx = self.get_outline_idx(outline_text)
                    in_outline.append(tmp_outline_idx)
                    tmp_y0 = int(x.y0)
                    tmp_y1 = int(x.y1)
                    outline_lines.append((tmp_y0, tmp_y1))
                    # print re.sub(self.replace,'',outline_text)
                    # print tmp_y0, tmp_y1
            # step 2: 再合并同一行的内容
            for i in range(1, len(in_outline)):
                if in_outline[i] == -1:
                    if in_outline[i - 1] != -1 and \
                            self.if_close_to(outline_lines[i][0], outline_lines[i - 1][0], mode='absolute',
                                             threshold=4) and \
                            self.if_close_to(outline_lines[i][1], outline_lines[i - 1][1], mode='absolute',
                                             threshold=4):
                        in_outline[i] = in_outline[i - 1]
            # print in_outline
            # raw_input()
            # step 3: 内容
            outline_content = {}
            tmp_x_idx = 0
            for x in layout:
                if (isinstance(x, LTTextBoxHorizontal)):
                    outline_text = x.get_text()
                    tmp_outline_idx = in_outline[tmp_x_idx]
                    if tmp_outline_idx != -1:
                        if tmp_outline_idx in outline_content.keys():
                            outline_content[tmp_outline_idx] += outline_text
                        else:
                            outline_content[tmp_outline_idx] = outline_text
                    tmp_x_idx += 1
            # step 4: 去除非目录内容

            tmp_outline_list_length = len(in_outline)
            for i in range(tmp_outline_list_length):
                is_real_outline_content = False
                if i > 0 and i < tmp_outline_list_length - 1 and in_outline[i - 1] != -1 and in_outline[i + 1] != -1:
                    is_real_outline_content = True
                elif i > 1 and in_outline[i - 1] != -1 and in_outline[i - 2] != -1:
                    is_real_outline_content = True
                elif i < tmp_outline_list_length - 2 and in_outline[i + 1] != -1 and in_outline[i + 2] != -1:
                    is_real_outline_content = True
                if not is_real_outline_content:
                    in_outline[i] = -1
            '''
            print in_outline
            # raw_input()
            for key in outline_content:
                print key
                print re.sub(self.replace,'',outline_content[key])
            raw_input()
            '''
            # 写入表格内容以外的其他内容
            x_idx = -1
            for x in layout:
                if (isinstance(x, LTTextBoxHorizontal)):  # if(isinstance(x, LTTextLineHorizontal)):
                    # print re.sub(self.replace,'',x.get_text())
                    x_idx += 1
                    if in_table[x_idx] != -1:
                        if not table_drawn[in_table[x_idx]]:
                            #########
                            if prev_text:
                                self.write2(prev_text.strip(), prev_align, prev_size, prev_weight, prev_indent)
                            prev_text = None
                            #########
                            # haven't drawn yet
                            self.draw_table(table_frames[in_table[x_idx]], page_xrange)
                            table_drawn[in_table[x_idx]] = True
                        continue
                    fontname, fontsize, location, line_width = self.get_font(x)
                    fontweight = self.fontweight_dict[fontname]
                    # 如果是outline
                    tmp_outline_idx = in_outline[x_idx]
                    if tmp_outline_idx != -1:
                        if not self.drawn_outline[tmp_outline_idx]:
                            #########
                            if prev_text:
                                self.write2(prev_text.strip(), prev_align, prev_size, prev_weight, prev_indent)
                            prev_text = None
                            #########
                            # print "draw outline here"
                            tmp_outline_title = outline_content[tmp_outline_idx]
                            self.draw_outline(tmp_outline_idx, tmp_outline_title, fontsize, fontweight)
                            self.drawn_outline[tmp_outline_idx] = True
                        continue
                    # text=re.sub(self.replace,'',x.get_text())
                    text = x.get_text()
                    actual_left = map_indents[location[0]]
                    indent = self.get_indent(actual_left, major_indents)
                    align = self.get_align(content_xrange, location, line_width, fontsize, major_size, debug=text)
                    if fontsize  == 0:
                        fontsize = 12
                    length = line_width / fontsize
                    # print x.x0, x.x1, x.y0, x.y1
                    # print text
                    # raw_input()
                    if (align == 'left'):
                        # 检测当前行是否是一行的开头，之前行是否已结尾
                        if prev_text == None:
                            prev_length = 0
                        ended = self.if_para_end(actual_left, major_indents, prev_length / typical_length)
                        if ended:
                            if prev_text:
                                self.write2(prev_text.strip(), prev_align, prev_size, prev_weight, prev_indent)
                            prev_text = None
                        # 准备传给下一次迭代
                        if prev_text:
                            prev_text = prev_text + text
                            prev_length = length
                        else:
                            prev_text = text
                            prev_size = fontsize
                            prev_weight = fontweight
                            prev_indent = indent
                            prev_align = align
                            prev_length = length
                    else:
                        if prev_text:
                            self.write2(prev_text.strip(), prev_align, prev_size, prev_weight, prev_indent)

                            prev_text = None
                        self.write2(text.strip(), align, fontsize, fontweight, 0, page_id=page_idx)



            self.level -= 1
            self.write('</div>')

        if prev_text:
            self.write2(prev_text.strip(), prev_align, prev_size, prev_weight, prev_indent)
        #print "#%s#"%self.page_html
        self.pages.append({'PageNo': page_idx, 'PageContent': self.page_html})
        self.page_html = ""
        with open(self.json_path,'w') as f:
            base_struct['Hits'][0]['Source']['Pages'] = self.pages
            base_struct['Hits'][0]['Source']['SubTitles'] = self.subtitles
            print >>f,json.dumps(base_struct, ensure_ascii=False)
        print "title"
        print json.dumps(self.subtitles, ensure_ascii=False)
        self.level -= 1
        self.write('</body>')

    def draw_outline(self, outline_idx, outline_title, font_size, font_weight):
        ref_id = self.outline_ids[outline_idx]
        level = self.outline_levels[outline_idx]
        '''
        print outline_title
        print outline_idx
        print ref_id
        print level
        print self.outline_titles[outline_idx]
        print self.outlines[ref_id][1]
        raw_input()
        '''
        if level > 0:
            indent = (level - 1) * 2.0
        else:
            indent = 0.0
        self.write('<p style="font-size:{0}px;font-weight:{1};text-indent:{2}em;" align="left">'.format( \
            font_size, font_weight, indent
        ))
        self.level += 1
        self.write('<a href="#{1}">{0}</a>'.format( \
            outline_title, ref_id
        ))
        self.level -= 1
        self.write('</p>')

    # self.write('<a style="font-size:{2}px;font-weight:{3};text-indent:{4}em;" align="left" href="#{1}">{0}</a>'.format(\
    #        outline_title, ref_id, font_size, font_weight, indent
    #    ))

    def get_outline_idx(self, goal_string):
        goal_idx = -1
        outline_length = len(self.outline_titles)
        clean_string = re.sub(self.replace, '', goal_string)
        len_string = len(clean_string)
        for i in range(outline_length):
            title = self.outline_titles[i]
            clean_title = re.sub(self.replace, '', title)
            len_title = len(clean_title)
            if len_title > len_string: continue
            if clean_title == clean_string[:len_title]:
                goal_idx = i
                break
        return goal_idx

    def draw_table(self, table_frame, page_xrange=None):
        # data = table_frame.data
        data, font, rowspan, colspan = table_frame.get_clean_data()
        if page_xrange:
            width_portion = 100.0 * (table_frame.range['max_x'] - table_frame.range['min_x']) / (
            page_xrange[1] - page_xrange[0])
            self.write('<table border="1" cellspacing="0" align="center" width="{0}%">'.format(int(width_portion)), True)
        else:
            self.write('<table border="1" cellspacing="0" align="center">', True)
        self.level += 1
        for i in range(len(data)):
            self.write('<tr>', True)
            self.level += 1
            for j in range(len(data[i])):
                content = data[i][j]
                fontsize = font[i][j]
                rs = rowspan[i][j]
                cs = colspan[i][j]
                candy = 'align=\"middle\"'
                res = re.search(r'[%\d,\.-]+', "".join(content))

                if res and res.group()=="".join(content):
                    candy = 'align=\"right\"'

                if fontsize:
                    self.write('<td  rowspan="{1}" colspan="{2}" {3}>{0}</td>'.format(
                        "<br>".join(content), rs, cs, candy), True)
                else:
                    self.write('<td rowspan="{1}" colspan="{2}" {3}>{0}</td>'.format("<br>".join(content), rs, cs, candy), True)
            self.level -= 1
            self.write('</tr>', True)
        self.level -= 1
        self.write('</table>', True)

    def get_font(self, x):
        default_fontname = self.chinese_str('ABCDEE+宋体')
        for line in x:
            line_width = line.width
            line_height = round(line.height)
            location = (round(line.x0), round(line.x1))
            # print line # LTTextLineHorizontal
            for char in line:
                if isinstance(char, LTAnno):
                    continue
                else:
                    fontsize = round(char.size)
                    fontname = char.fontname  # ABCDEE-黑体 即加粗 ABCDEE-宋体 即不加粗
                    if fontname in self.fontweight_dict.keys():
                        return fontname, fontsize, location, line_width
            return default_fontname, line_height, location, line_width

    def get_indent(self, actual_left, major_indents):
        level_indent = max(major_indents[0], major_indents[1])
        if actual_left == level_indent:
            return 2.0
        else:
            return 0.0

    def get_indent_info(self, layout, page_xrange):
        most_left = page_xrange[1]
        most_right = page_xrange[0]
        indent_list = {}
        fontsize_list = {}
        for x in layout:
            if (isinstance(x, LTTextBoxHorizontal)):
                fontname, fontsize, location, line_width = self.get_font(x)
                if location[0] < most_left:
                    most_left = location[0]
                if location[1] > most_right:
                    most_right = location[1]
                if fontsize in fontsize_list.keys():
                    fontsize_list[fontsize] += 1
                else:
                    fontsize_list[fontsize] = 1
                indent = location[0]
                if indent in indent_list.keys():
                    indent_list[indent] += 1
                else:
                    indent_list[indent] = 1
            #elif (isinstance(x, LTFigure)):
        return (most_left, most_right), indent_list, fontsize_list

    def if_close_to(self, src, dst, mode='percent', threshold=0.1):
        if mode == 'percent':
            if (src >= dst * (1 - threshold)) and (src <= dst * (1 + threshold)):
                return True
            return False
        elif mode == 'absolute':
            if (src >= dst - threshold) and (src <= dst + threshold):
                return True
            return False

    def get_conclude(self, indent_list, fontsize_list):
        sorted_indents = self.sort_dict_by_val(indent_list)
        sorted_sizes = self.sort_dict_by_val(fontsize_list)
        mapping_list = {}
        for key in indent_list.keys():
            mapping_list[key] = key
        max_amount_indent = sorted_indents[0][0]
        max_amount_indent_2 = -1
        for item in sorted_indents[1:]:
            if self.if_close_to(item[0], max_amount_indent):
                mapping_list[item[0]] = max_amount_indent
            else:
                if max_amount_indent_2 == -1:  # 尚未决定第二缩进
                    max_amount_indent_2 = item[0]
                else:
                    if self.if_close_to(item[0], max_amount_indent_2):
                        mapping_list[item[0]] = max_amount_indent_2
                    else:
                        break
        max_amount_size = sorted_sizes[0][0]
        return (max_amount_indent, max_amount_indent_2), mapping_list, max_amount_size

    def get_align(self, content_xrange, location, line_width, fontsize, major_size, debug=None):
        threshold = 0.8
        ratio_lim = 0.67
        width_lim = 0.7
        size_threshold = 1.2
        percentage = line_width / (content_xrange[1] - content_xrange[0])
        delta_left = location[0] - content_xrange[0]
        delta_right = content_xrange[1] - location[1]
        delta1 = max(delta_left, delta_right)
        delta2 = min(delta_left, delta_right)
        ratio = None
        if delta1 != 0:
            ratio = delta2 / delta1
        else:  # delta2 <= delta1 = 0
            return "left"
        if ratio >= ratio_lim and (percentage < threshold or fontsize > major_size * size_threshold):
            return "center"
        if ratio < ratio_lim and percentage < width_lim:
            if delta_left < delta_right:
                return "left"
            else:
                return "right"
        return "left"

    def if_para_end(self, actual_left, major_indents, ratio):
        threshold = 0.7
        min_indent = min(major_indents[0], major_indents[1])
        if actual_left == min_indent:
            # 除非此行比较短，否则认定为没有分段
            if ratio < threshold:
                return True
            return False
        else:
            return True

    def is_line(self, rect_elem):
        threshold = 3  # 2
        x_diff = rect_elem.x1 - rect_elem.x0
        y_diff = rect_elem.y1 - rect_elem.y0
        if x_diff < threshold:
            if y_diff > 3 * threshold:
                return "y"
            else:
                return "point"
        if y_diff < threshold:
            if x_diff > 3 * threshold:
                return "x"
            else:
                return "point"
        return False
    def show_page_layout_points(self, layout, points, raw_lines=None):
        page_range = {
            "left": layout.x0,
            "right": layout.x1,
            "top": layout.y1,
            "bottom": layout.y0
        }

        #turtle.tracer(False)
        print "Page Range = left:{0}, right: {1}, top: {2}, bottom: {3}".format( \
            page_range["left"], page_range["right"], page_range["top"], page_range["bottom"])
        offset_x = -1.0 * (page_range["right"] + page_range["left"]) / 2.0
        offset_y = -1.0 * (page_range["top"] + page_range["bottom"]) / 2.0
        size_x = 1.5 * (page_range["right"] - page_range["left"])
        size_y = 1.5 * (page_range["top"] - page_range["bottom"])
        draw = Draw(size_x, size_y, offset_x, offset_y)
        draw.set_color("black")
        draw.square(page_range["left"], page_range["right"], page_range["top"], page_range["bottom"])

        for p in points:
            #for p in tp:
            x,y = p[0],p[1]
            draw.dot(x,y)
        if raw_lines:
            for p in raw_lines:
                draw.line(p[0][0], p[0][1], p[1][0], p[1][1])
        draw.done()
        time.sleep(10)

    def show_page_layout_lines(self, layout, lines):
        page_range = {
            "left": layout.x0,
            "right": layout.x1,
            "top": layout.y1,
            "bottom": layout.y0
        }

        #turtle.tracer(False)
        print "Page Range = left:{0}, right: {1}, top: {2}, bottom: {3}".format( \
            page_range["left"], page_range["right"], page_range["top"], page_range["bottom"])
        offset_x = -1.0 * (page_range["right"] + page_range["left"]) / 2.0
        offset_y = -1.0 * (page_range["top"] + page_range["bottom"]) / 2.0
        size_x = 1.5 * (page_range["right"] - page_range["left"])
        size_y = 1.5 * (page_range["top"] - page_range["bottom"])
        draw = Draw(size_x, size_y, offset_x, offset_y)
        draw.set_color("black")
        draw.square(page_range["left"], page_range["right"], page_range["top"], page_range["bottom"])

        #for p in lines:
            #for p in tline['box']:
            #p = tline['box']
        #    draw.line(p[0][0], p[0][1], p[1][0], p[1][1])
        #    print p[0][0], p[0][1], p[1][0], p[1][1]
        #    draw.square(p[0][0],p[1][0], p[1][1],p[0][1])
        for p in lines:
            #for p in t_lines:
            draw.line(p['x0'], p['y0'], p['x1'], p['y1'])

        draw.done()
        time.sleep(10)
    def show_page_layout_post(self, layout, lines):
        page_range = {
            "left": layout.x0,
            "right": layout.x1,
            "top": layout.y1,
            "bottom": layout.y0
        }

        #turtle.tracer(False)
        print "Page Range = left:{0}, right: {1}, top: {2}, bottom: {3}".format( \
            page_range["left"], page_range["right"], page_range["top"], page_range["bottom"])
        offset_x = -1.0 * (page_range["right"] + page_range["left"]) / 2.0
        offset_y = -1.0 * (page_range["top"] + page_range["bottom"]) / 2.0
        size_x = 1.5 * (page_range["right"] - page_range["left"])
        size_y = 1.5 * (page_range["top"] - page_range["bottom"])
        draw = Draw(size_x, size_y, offset_x, offset_y)
        draw.set_color("black")
        draw.square(page_range["left"], page_range["right"], page_range["top"], page_range["bottom"])

        for line in lines:
            for idx,l in enumerate(line):
                if idx%2==0:
                    draw.set_color("orange")
                else:
                    draw.set_color("red")
                left = l[0][0]
                right = l[1][0]
                bottom = l[0][1]
                top = l[1][1]

                draw.square(left, right, top, bottom)
        """
        for l in lines:
            draw.set_color("orange")
            left = l['x0']
            right = l['x1']
            top = l['y1']
            bottom = l['y0']
            isLine = l['isLine']
            print "left:{0}, right: {1}, top: {2}, bottom: {3}".format(left, right, top, bottom)
            if isLine == 'x':
                fixed_y = (top + bottom) / 2.0
                draw.line(left, fixed_y, right, fixed_y)
            elif isLine == 'y':
                fixed_x = (left + right) / 2.0
                draw.line(fixed_x, top, fixed_x, bottom)
            else:
                draw.square(left, right, top, bottom)
        """
        draw.done()
        time.sleep(10)

    def show_page_layout(self, layout):
        page_range = {
            "left": layout.x0,
            "right": layout.x1,
            "top": layout.y1,
            "bottom": layout.y0
        }
        print "Page Range = left:{0}, right: {1}, top: {2}, bottom: {3}".format( \
            page_range["left"], page_range["right"], page_range["top"], page_range["bottom"])
        offset_x = -1.0 * (page_range["right"] + page_range["left"]) / 2.0
        offset_y = -1.0 * (page_range["top"] + page_range["bottom"]) / 2.0
        size_x = 1.5 * (page_range["right"] - page_range["left"])
        size_y = 1.5 * (page_range["top"] - page_range["bottom"])
        draw = Draw(size_x, size_y, offset_x, offset_y)
        draw.set_color("black")
        draw.square(page_range["left"], page_range["right"], page_range["top"], page_range["bottom"])
        idx = 0
        for x in layout:
            isLine = False
            if (isinstance(x, LTTextBoxHorizontal)):

                for line in x:
                    # print line # LTTextLine
                    #draw.set_color("green")
                    if line.x1 - line.x0 > 12:
                        draw.square(line.x0, line.x1, line.y1, line.y0)
                    for char in line:
                        # print char # LTChar / LTAnno
                        if isinstance(char, LTChar):
                            draw.set_color("brown")
                            res = re.sub(r'\s+', '', char.get_text())
                            if  len(res) > 0:
                                draw.square(char.x0, char.x1, char.y1, char.y0)
                            else:
                                print "#%s#"%char.get_text()
                            print char.get_text()
                        elif isinstance(char, LTChar):
                            draw.set_color("blue")
                            draw.square(char.x0, char.x1, char.y1, char.y0)
                draw.set_color("black")

                pass
            elif (isinstance(x, LTRect)):

                isLine = self.is_line(x)

                #if isLine:
                idx +=1
                if idx%2==0:
                    draw.set_color("orange")
                else:
                    draw.set_color("red")
            else:
                # print x
                # raw_input()
                draw.set_color("blue")


            left = x.x0
            right = x.x1
            top = x.y1
            bottom = x.y0
            print "left:{0}, right: {1}, top: {2}, bottom: {3}".format(left, right, top, bottom)
            if isLine == 'x':
                fixed_y = (top + bottom) / 2.0
                draw.line(left, fixed_y, right, fixed_y)
            elif isLine == 'y':
                fixed_x = (left + right) / 2.0
                draw.line(fixed_x, top, fixed_x, bottom)
            else:
                pass
                #if (right - left) > 12:
                #    print right - left
                #    draw.square(left, right, top, bottom)

        draw.done()
        time.sleep(10)
        #return layout

    def get_closest_idx(self, goal_value, lst, threshold):
        closest_idx = -1
        for i in range(len(lst)):
            item = lst[i]
            if abs(item - goal_value) <= threshold:
                closest_idx = i
                break
        return closest_idx

    def split_table(self, y_and_sx):
        my_tables = []
        if len(y_and_sx) < 1:
            return [],[]
        sorted_lines = y_and_sx
        last_line = sorted_lines[0]
        my_tables = [[last_line]]
        for i in range(1, len(sorted_lines)):
            # 分段数相同，位置完全相等

            same_table = False

            # if len(last_line[1]) == len(sorted_lines[i][1]):
            #     same_table = True
            #     for k in range(len(last_line)-1, 0, -1):
            #         if not same(last_line[1][k], sorted_lines[i][1][k]):
            #             same_table = False
            #             break
            # 短线点集是长线点集子集的，合并
            if len(last_line[1]) >= len(sorted_lines[i][1]):
                same_table = is_sub_list(last_line[1], sorted_lines[i][1])
            else:
                same_table = is_sub_list(sorted_lines[i][1], last_line[1])

            if same_table:
                my_tables[-1].append(sorted_lines[i])
            else:
                my_tables.append([sorted_lines[i]])
            last_line = sorted_lines[i]

        single_table_id = []
        # 把单一线 添加到临近的表格上去，
        # 向下合并，单线一定要给到，点数比自己多的上边去，不然表格不封闭
        for idx, t in enumerate(my_tables):
            if len(t) == 1:
                single_table_id.append(idx)
        # 单一线和其他数据的分段数不同，若是在表头处，需要添加一条水平直线，对表头做切割。

        merge_pair = []
        for idx in single_table_id:
            prex_line = []
            next_line = []
            if idx > 0:
                prex_line = my_tables[idx - 1][-1][1]
            if idx + 1 < len(my_tables):
                next_line = my_tables[idx + 1][0][1]
            same_prex = 0
            same_next = 0
            for p in my_tables[idx][0][1]:
                for p_prex in prex_line:
                    if same(p, p_prex):
                        same_prex += 1
                for p_next in next_line:
                    if same(p, p_next):
                        same_next += 1
            # 优先做表头的线
            if same_next > same_prex:
                if same_next > 1:
                    merge_pair.append((idx, idx + 1))
            else:
                if same_prex > 1:  # 控制合并时的 相似点数量
                    if (idx - 1, idx) not in merge_pair:
                        merge_pair.append((idx, idx - 1))

        skip_segs = {}
        # 反向遍历列表,

        for pair in merge_pair[::-1]:
            for l in my_tables[pair[0]]:
                # print l
                # 0 是下边的table, 1 是上边的table
                if pair[0] < pair[1]:
                    my_tables[pair[1]].insert(0, l)
                else:
                    top_line = my_tables[pair[1]][-1]
                    # 向下合并，当表头
                    # 说明表头存在单元格合并，需要增加水平线
                    if len(top_line[1]) > len(l[1]):
                        ave_y = (top_line[0] + l[0]) / 2
                        skip_segs[ave_y] = 0
                        # split_l = (ave_y, top_line[1])
                        # my_tables[pair[1]].append(split_l)
                        # add_segs(top_line[1][1:], ave_y, table_outline_elem_lst)
                    my_tables[pair[1]].append(l)
            del my_tables[pair[0]]
            # print len(my_tables)

            # 保证 表尾的分段数量部大于表头
        for idx in range(len(my_tables) - 1, 0, -1):
            my_tables[idx].sort()
            t = my_tables[idx]
            if len(t[-1][1]) > len(t[0][1]):  # 表头大于表尾，考虑与下一个表格合并
                if len(t[-1][1]) == len(my_tables[idx - 1][1][-1]):  # 表头和下方表头 相同，考虑合并
                    for l in t:
                        my_tables[idx - 1].append(l)
                    del my_tables[idx]
        # 对短直线做修正,至少和表尾相同
        for idx, t in enumerate(my_tables):
            for l_id, line in enumerate(t):
                if len(line[1]) < len(t[0][1]) and l_id < len(t) - 1:  # 表头不参与
                    my_tables[idx][l_id] = (line[0], t[0][1])

        return my_tables,skip_segs
    #################
    # steps in get_tables
    # step 1
    def get_tables_elements(self, layout, text_cols):
        max_stroke = -1
        table_outline_elem_lst = []  # contents: {'x0': x0, 'x1': x1, 'y0': y0, 'y1': y1, 'isLine': isLine}
        table_raw_dash_lst = []
        dashline_parser_xs = []
        dashline_parser_ys = []
        slash_elem_lst = {}
        y_and_its_xs = {}
        num_horizon_line = 0
        num_vertical_line = 0


        for x in layout:
            # if(isinstance(x, LTRect)):

            if isinstance(x, LTRect) or isinstance(x, LTFigure):
                left = x.x0
                right = x.x1
                top = x.y1
                bottom = x.y0
                left = int(left)
                right = int(right)
                top = int(top)
                bottom = int(bottom)
                isLine = self.is_line(x)
                """
                if isinstance(x,LTLine):
                    if isLine == 'x':
                        top -= 1
                        bottom += 1
                    else:
                        left -= 1
                        right += 1
                """
                if isLine:  # a line
                    # fetch data
                    if isLine == 'x':
                        num_horizon_line += 1
                        line_stroke = top - bottom
                        shared_y = (top + bottom) / 2.0
                        if shared_y not in dashline_parser_ys:
                            dashline_parser_ys.append(shared_y)
                        if left not in dashline_parser_xs:
                            dashline_parser_xs.append(left)
                        if right not in dashline_parser_xs:
                            dashline_parser_xs.append(right)
                        flag = True
                        for k in y_and_its_xs:
                            if same(shared_y, k):
                                y_and_its_xs[k].add(left)
                                y_and_its_xs[k].add(right)
                                flag = False
                                break
                        if flag:
                            y_and_its_xs[shared_y] = set()  # 去重相近的重复线
                            y_and_its_xs[shared_y].add(left)
                            y_and_its_xs[shared_y].add(right)
                    elif isLine == 'y':
                        num_vertical_line +=1
                        line_stroke = right - left
                        shared_x = (left + right) / 2.0
                        if shared_x not in dashline_parser_xs:
                            dashline_parser_xs.append(shared_x)
                        if top not in dashline_parser_ys:
                            dashline_parser_ys.append(top)
                        if bottom not in dashline_parser_ys:
                            dashline_parser_ys.append(bottom)
                    elif isLine == 'point':
                        line_stroke = min(top - bottom, right - left)  # max?
                    # update data
                    if line_stroke > max_stroke:
                        max_stroke = line_stroke
                if isLine:
                    tmp_elem = {
                        'x0': left,
                        'x1': right,
                        'y0': bottom,
                        'y1': top,
                        'isLine': isLine
                    }
                    if isLine == 'point':
                        table_raw_dash_lst.append(tmp_elem)
                    elif isLine == 'y':
                        pass
                        #tmp_elem['x1'] = tmp_elem['x0']
                        slash_elem_lst[(bottom,top)] = 0
                        #table_outline_elem_lst.append(tmp_elem)
                         # if  tmp_elem['x1'] == tmp_elem['x0']:
                         #     table_outline_elem_lst.append(tmp_elem)
                         # else:
                         #     tmp_elem['x1'] = tmp_elem['x0']
                         #     slash_elem_lst.append(tmp_elem)



        #remove y-line that is too close
        #remove_y_id = []
        #for p in table_outline_elem_lst:

        #remove point that is too close
        for k in y_and_its_xs:

            a = sorted(list(y_and_its_xs[k]))
            last_p = a[0]
            remove_id = []
            if len(a) > 10:
                pass
            for i in range(1,len(a)):
                if same(last_p, a[i]):
                    if i == 1: #最左对，移除靠右
                        remove_id.insert(0, 1)
                    else:
                        remove_id.insert(0, i-1)
                        last_p = a[i]
                else:
                    last_p = a[i]
            for idx in remove_id:
                del a[idx]

            y_and_its_xs[k] = a
        y_and_sx = sorted(y_and_its_xs.iteritems(), key=lambda x: x[0])

        #移除页眉线和页脚线
        if y_and_sx is not None and len(y_and_sx) > 1:
            if len(y_and_sx[0][1]) == 2:
                del y_and_sx[0]
            if len(y_and_sx[-1][1]) == 2:
                del y_and_sx[-1]

        # 删除过短的线段
        for idx, l in enumerate(y_and_sx):
            last_p = l[1][0]
            pairs = []
            for i in range(1, len(l[1])):
                if abs(last_p - l[1][i]) <= 15:  # 12 is the size of a char
                    pairs.insert(0, [i - 1, i])
                last_p = l[1][i]
            for prex, curr in pairs:
                if prex == 0:
                    del y_and_sx[idx][1][curr]  # 如果是最左边，删除靠右的
                else:
                    del y_and_sx[idx][1][prex]
            y_and_sx[idx][1].sort()
            # add_segs(l[1],l[0],table_outline_elem_lst)

        #利用文本补全 最上和最下的表格线
        uu = []
        for l in text_cols:
            uu.append([l['box'][0][1], l['box'][1][1], len(l['text_lines'])])
        uu.sort(key=lambda x: x[0])
        if len(uu) > 0 and len(y_and_sx) > 1:
            bot_line = y_and_sx[0]
            top_line = y_and_sx[-1]
            for text_line in uu:
                if text_line[0] < bot_line[0]:
                    #text_line[2]表示的是矩形的个数
                    if len(bot_line[1]) == text_line[2] + 1: # 左下角
                        y_and_sx.insert(0, [text_line[0],bot_line[1]])
                        break
                else:
                    break
            for text_line in uu[::-1]:
                if text_line[1] > top_line[0]:
                    if len(top_line[1]) == text_line[2] + 1: # 右上角
                        y_and_sx.append([text_line[1], top_line[1]])
                        break
                else:
                    break
            #pass


        # split_tables
        my_tables = []
        if  num_horizon_line > 2 and num_vertical_line < 2:
            my_tables, skip_segs = self.split_table(y_and_sx)
            for idx,t in enumerate(my_tables):
                #找到 最大y,最小y 切分数据
                t.sort(key=lambda x: x[0], reverse=True)  #从表头向表尾
                up = t[0][0] #top y
                bottom = t[-1][0]
                ys = []
                last_y = 0
                text_box = []
                for l in text_cols:
                    if in_range(l['box'][0][1], bottom, up):
                        text_box.append([l['box'][0][1],l['box'][1][1]])
                text_box.sort(key= lambda x:x[0])
                if len(text_box) == 0:
                    continue
                last_box = text_box[0]
                show_up = False
                for i in range(1,len(text_box)):
                    y = (last_box[1] + text_box[i][0])/2
                    last_box = text_box[i]
                    ys.append(y)
                    my_tables[idx].append((y,t[-1][1],'text'))
                    #增加横线
                    #add_segs(t[-1][1], y, table_outline_elem_lst)

            # 写出 水平分段
           # for i in range(len(my_tables)):

                # for l in my_tables[i]:
                #    if l[0] not in skip_segs:
                #        add_segs(l[1], l[0], table_outline_elem_lst)

            for i in range(len(my_tables)):
                my_tables[i].sort(key=lambda x:x[0])
                merge_ys(my_tables[i])
                uniform_segs(my_tables[i])

                for l in my_tables[i]:
                    if l[0] not in skip_segs:
                        add_segs(l[1], l[0], table_outline_elem_lst)
                # 表头分割 单独画
                split_l = sheet_head_split(my_tables[i])
                if split_l:
                    start = split_l[2]
                    add_segs(split_l[1][start:], split_l[0], table_outline_elem_lst)
                    my_tables[i].append(split_l)

            for t in my_tables:
                t.sort(key=lambda x: x[0])
                for i in range(1, len(t)):
                    last_line = t[i - 1]
                    for j in range(len(last_line[1])):

                        x = last_line[1][j]
                        tmp_elem = {
                            'x0': x,
                            'x1': x,
                            'y0': last_line[0],
                            'y1': t[i][0],
                            'isLine': 'y'
                        }
                        table_outline_elem_lst.append(tmp_elem)
        else:

            # 移除距离太近的y
            if len(y_and_sx) > 0:
                del_ids = []
                last_l = y_and_sx[0]
                for i in range(1, len(y_and_sx)):
                    if abs(last_l[0] - y_and_sx[i][0]) < 12: # 距离太近
                        if len(y_and_sx[i][1]) < len(last_l[1]):
                            del_ids.insert(0, i)
                        else:
                            del_ids.insert(0, i-1)
                            last_l = y_and_sx[i]
                    else:
                        last_l = y_and_sx[i]
                for idx in del_ids:
                    del y_and_sx[idx]

            #用竖线进行表格分割，先求竖线分段
            segs = split_lines(slash_elem_lst)
            my_tables= []
            for s in segs:
                t = []
                for l in y_and_sx:
                    if l[0] > s[0]-12 and l[0]<s[1]+12:
                        t.append(l)
                my_tables.append(t)


            #补全短直线 && 保证两侧对齐
            for i,t in enumerate(my_tables):
                left = 1000
                right = 0
                for l in t:
                    left = min(l[1][0], left)
                    right = max(l[1][-1], right)
                #保证表格封闭
                for j,l in enumerate(my_tables[i]):
                    li = l[1]
                    if not same(l[1][0],left):
                        li.insert(0, left)
                    if not same(l[1][-1], right):
                        li.append(right)
                    my_tables[i][j] = (l[0], li)

                for j in range(1,len(my_tables[i])-1):
                    if len(my_tables[i][j][1]) < len(my_tables[i][j-1][1]):
                        my_tables[i][j]=(my_tables[i][j][0],my_tables[i][j-1][1])



            #画横线
            for l in y_and_sx:
                add_segs(l[1], l[0], table_outline_elem_lst)
            #画竖线
            for t in my_tables:
                t.sort(key=lambda x: x[0])
                for i in range(1, len(t)):
                    last_line = t[i - 1]
                    for j in range(len(last_line[1])):
                        x = last_line[1][j]
                        tmp_elem = {
                            'x0': x,
                            'x1': x,
                            'y0': last_line[0],
                            'y1': t[i][0],
                            'isLine': 'y'
                        }
                        table_outline_elem_lst.append(tmp_elem)

        lines = []
        points = {}
        for x in layout:
            if isinstance(x, LTLine):
                left = x.x0
                right = x.x1
                top = x.y1
                bottom = x.y0
                # if same(x.x0, x.x1) or same(x.y0, x.y1): # 是dot
                #    continue
                flag = True

                for t in my_tables:
                    if in_range(x.y0, t[0][0], t[-1][0]) or in_range(x.y1, t[0][0], t[-1][0]):
                        flag = False
                        break
                if flag:
                    lines.append([(x.x0, x.y0), (x.x1, x.y1)])
                #else:
                #    pass
        # lines = merge_same_line(raw_lines)

        for seg in self.add_cross_point(lines, points):
            direct = 'x'
            if seg[0][0] == seg[1][0]:  # vertical
                direct = 'y'
            tmp_elem = {
                'x0': seg[0][0],
                'y0': seg[0][1],
                'x1': seg[1][0],
                'y1': seg[1][1],
                'isLine': direct
            }
            table_outline_elem_lst.append(tmp_elem)



        #raw_lines = []


        #print len(table_raw_dash_lst),len(table_outline_elem_lst)

    ###

        if max_stroke >= 0:
            bias = self.bias_param[0] * max_stroke  # 3 # 2 # 1.5
        else:
            bias = self.bias_param[1]  # 5 # 3 # 2
        return bias, table_outline_elem_lst, table_raw_dash_lst, dashline_parser_xs, dashline_parser_ys

    # aid function
    def line_merge(self, range1, range2, bias=0):
        assert len(range1) == 2 and len(range2) == 2, "range should be an array containing 2 elements"
        try:
            r1_min = min(range1) - bias
            r1_max = max(range1) + bias
            r2_min = min(range2) - bias
            r2_max = max(range2) + bias
        except Exception,ex:
            pass
        if (r1_min - r2_min) * (r1_min - r2_max) <= 0 or (r1_max - r2_min) * (r1_max - r2_max) <= 0 \
                or (r2_min - r1_min) * (r2_min - r1_max) <= 0 or (r2_max - r1_min) * (r2_max - r1_max) <= 0:
            merged_range = [[min(r1_min, r2_min) + bias, max(r1_max, r2_max) - bias]]
        else:
            merged_range = [range1, range2]
        return merged_range

    # step 2
    def get_tables_dashlines(self, table_raw_dash_lst, bias):
        # 处理一下 table_outline_elem_lst
        # 首先把虚线找出来连起来
        raw_dashline_dot_xs = {}  # (x1, x2): [idx1, idx2, ...]
        raw_dashline_dot_ys = {}  # (y1, y2): [idx1, idx2, ...]
        for i in range(len(table_raw_dash_lst)):
            raw_dashline_dots = table_raw_dash_lst[i]
            left = raw_dashline_dots['x0']
            right = raw_dashline_dots['x1']
            top = raw_dashline_dots['y1']
            bottom = raw_dashline_dots['y0']
            # draw.square(left, right, top, bottom)
            dot_x_key = (left, right)
            dot_y_key = (bottom, top)
            if dot_x_key in raw_dashline_dot_xs.keys():
                raw_dashline_dot_xs[dot_x_key].append([bottom, top])
            else:
                raw_dashline_dot_xs[dot_x_key] = [[bottom, top]]
            if dot_y_key in raw_dashline_dot_ys.keys():
                raw_dashline_dot_ys[dot_y_key].append([left, right])
            else:
                raw_dashline_dot_ys[dot_y_key] = [[left, right]]
        # lines merged
        table_dashlines = []  # contents: element
        for dot_x_key in raw_dashline_dot_xs.keys():  # vertical lines
            # 针对每一个 x 线段，找这个坐标上能连起来的y线段；因为预先排序，所以只需要看前一个就行
            candidate_ys = raw_dashline_dot_xs[dot_x_key]
            candidate_ys.sort()
            first_line = [candidate_ys[0][0], candidate_ys[0][1]]
            lines_y_list = [first_line]
            for dot_y in candidate_ys[1:]:
                last_y_idx = len(lines_y_list) - 1
                last_line = lines_y_list[last_y_idx]
                # print line_merge(last_line, dot_y, bias=bias)
                merged_result = self.line_merge(last_line, dot_y, bias=bias)
                if len(merged_result) == 1:
                    # successfully merged
                    lines_y_list[last_y_idx][0] = merged_result[0][0]
                    lines_y_list[last_y_idx][1] = merged_result[0][1]
                else:
                    lines_y_list.append([dot_y[0], dot_y[1]])
            # raw_input("******ended dot {0}*********".format(dot_x_key))
            left = min(dot_x_key[0], dot_x_key[1])
            right = max(dot_x_key[0], dot_x_key[1])
            for line_y in lines_y_list:
                bottom = min(line_y[1], line_y[0])
                top = max(line_y[1], line_y[0])

                if top - bottom > 2 * bias:
                    tmp_elem = {
                        'x0': left,
                        'x1': right,
                        'y0': bottom,
                        'y1': top,
                        'isLine': 'y'
                    }
                    table_dashlines.append(tmp_elem)

        for dot_y_key in raw_dashline_dot_ys.keys():
            # 对y同理
            candidate_xs = raw_dashline_dot_ys[dot_y_key]
            candidate_xs.sort()
            first_line = [candidate_xs[0][0], candidate_xs[0][1]]
            lines_x_list = [first_line]
            for dot_x in candidate_xs[1:]:
                last_x_idx = len(lines_x_list) - 1
                last_line = lines_x_list[last_x_idx]
                merged_result = self.line_merge(last_line, dot_x, bias=bias)
                if len(merged_result) == 1:
                    lines_x_list[last_x_idx][0] = merged_result[0][0]
                    lines_x_list[last_x_idx][1] = merged_result[0][1]
                else:
                    lines_x_list.append([dot_x[0], dot_x[1]])
            top = max(dot_y_key[0], dot_y_key[1])
            bottom = min(dot_y_key[0], dot_y_key[1])
            for line_x in lines_x_list:
                left = min(line_x[0], line_x[1])
                right = max(line_x[0], line_x[1])
                if right - left > 2 * bias:
                    tmp_elem = {
                        'x0': left,
                        'x1': right,
                        'y0': bottom,
                        'y1': top,
                        'isLine': 'x'
                    }
                    table_dashlines.append(tmp_elem)
        return table_dashlines

    # step 2.1: 合并dashline到其他表格边框元素列表之中
    def get_tables_elements_all(self, table_outline_elem_lst, table_dashlines, dashline_parser_xs, dashline_parser_ys):
        for dashline in table_dashlines:
            if dashline['isLine'] == 'x':
                # horizontal
                start_val = min(dashline['x0'], dashline['x1'])
                end_val = max(dashline['x0'], dashline['x1'])
                start_idx = -1
                end_idx = -1
                for i in range(len(dashline_parser_xs)):
                    if dashline_parser_xs[i] == start_val:
                        start_idx = i
                    if dashline_parser_xs[i] == end_val:
                        end_idx = i
                        break
                assert start_idx != -1 and end_idx != -1 and start_idx <= end_idx, "1# {0}, {1} not in {2}".format(
                    start_val, end_val, dashline_parser_xs)
                for i in range(start_idx, end_idx):
                    table_outline_elem_lst.append({
                        'x0': dashline_parser_xs[i],
                        'x1': dashline_parser_xs[i + 1],
                        'y0': dashline['y0'],
                        'y1': dashline['y1'],
                        'isLine': 'x'
                    })
            elif dashline['isLine'] == 'y':
                # horizontal
                start_val = min(dashline['y0'], dashline['y1'])
                end_val = max(dashline['y0'], dashline['y1'])
                start_idx = -1
                end_idx = -1
                for i in range(len(dashline_parser_ys)):
                    if dashline_parser_ys[i] == start_val:
                        start_idx = i
                    if dashline_parser_ys[i] == end_val:
                        end_idx = i
                        break
                assert start_idx != -1 and end_idx != -1 and start_idx <= end_idx, "2# {0}, {1} not in {2}".format(
                    start_val, end_val, dashline_parser_ys)
                for i in range(start_idx, end_idx):
                    table_outline_elem_lst.append({
                        'x0': dashline['x0'],
                        'x1': dashline['x1'],
                        'y0': dashline_parser_ys[i],
                        'y1': dashline_parser_ys[i + 1],
                        'isLine': 'y'
                    })
        return table_outline_elem_lst

    # step 3: 分出大致区域
    def get_tables_areas(self, table_outline_elem_lst, bias):
        # 粗略分出不同表格的子区域
        clean_tables_area = []  # 每个表占的x, y范围, 内容: [[x1, x2], [y1, y2]]

        for outline_elem in table_outline_elem_lst:
            tmp_x_range = [outline_elem['x0'], outline_elem['x1']]
            tmp_y_range = [outline_elem['y1'], outline_elem['y0']]
            i = len(clean_tables_area) - 1
            while i >= 0:
                new_x_range = self.line_merge(clean_tables_area[i][0], tmp_x_range, bias=bias)
                new_y_range = self.line_merge(clean_tables_area[i][1], tmp_y_range, bias=bias)
                # print clean_tables_area[i][0], tmp_x_range, new_x_range
                # print clean_tables_area[i][1], tmp_y_range, new_y_range
                if len(new_x_range) == 1 and len(new_y_range) == 1:
                    # successfully merged
                    tmp_x_range[0] = new_x_range[0][0]
                    tmp_x_range[1] = new_x_range[0][1]
                    tmp_y_range[0] = new_y_range[0][0]
                    tmp_y_range[1] = new_y_range[0][1]
                    clean_tables_area.pop(i)
                i -= 1
            clean_tables_area.append([tmp_x_range, tmp_y_range])
        clean_tables_lst = []  # grouped outline elements, contents: [elem1, elem2, ...]
        for elem in clean_tables_area:
            clean_tables_lst.append([])
        for outline_elem in table_outline_elem_lst:
            tmp_x_range = [outline_elem['x0'], outline_elem['x1']]
            tmp_y_range = [outline_elem['y1'], outline_elem['y0']]
            tmp_table_idx = -1
            for i in range(len(clean_tables_area)):
                new_x_range = self.line_merge(clean_tables_area[i][0], tmp_x_range, bias=bias)
                new_y_range = self.line_merge(clean_tables_area[i][1], tmp_y_range, bias=bias)
                if len(new_x_range) == 1 and len(new_y_range) == 1:
                    tmp_table_idx = i
                    break
            if tmp_table_idx >= 0:
                clean_tables_lst[tmp_table_idx].append(outline_elem.copy())
        return clean_tables_lst

    # step 4:
    def get_tables_raw_frame(self, clean_tables_lst, bias):
        raw_lines = []  # contents: ((x1, y1), (x2, y2))
        raw_points = {}  # contents: (x, y): [idx1, idx2, ...] - the index of corresponding lines
        points_visited = {}  # contents: (x, y) : True / False
        for clean_tables_lst_elem in clean_tables_lst:
            raw_points_x = []  # contents: x
            raw_points_y = []  # contents: y
            for outline_elem in clean_tables_lst_elem:
                left = outline_elem['x0']
                right = outline_elem['x1']
                top = outline_elem['y1']
                bottom = outline_elem['y0']
                idx_left = self.get_closest_idx(left, raw_points_x, bias)
                idx_right = self.get_closest_idx(right, raw_points_x, bias)
                idx_top = self.get_closest_idx(top, raw_points_y, bias)
                idx_bottom = self.get_closest_idx(bottom, raw_points_y, bias)
                if idx_left >= 0:
                    left = raw_points_x[idx_left]
                if idx_right >= 0:
                    right = raw_points_x[idx_right]
                if idx_top >= 0:
                    top = raw_points_y[idx_top]
                if idx_bottom >= 0:
                    bottom = raw_points_y[idx_bottom]

                isLine = outline_elem['isLine']
                if isLine:  # a line
                    # fetch data
                    if isLine == 'x':
                        # print 'x'
                        if idx_left == -1:
                            raw_points_x.append(left)
                        idx_right = self.get_closest_idx(right, raw_points_x, bias)
                        if idx_right == -1:
                            raw_points_x.append(right)
                        fixed_y = (top + bottom) / 2.0
                        #fixed_y = int(fixed_y)
                        idx_fixed_y = self.get_closest_idx(fixed_y, raw_points_y, bias)
                        if idx_fixed_y >= 0:
                            fixed_y = raw_points_y[idx_fixed_y]
                        else:
                            raw_points_y.append(fixed_y)

                        pt1 = (left, fixed_y)
                        pt2 = (right, fixed_y)
                    elif isLine == 'y':
                        # print 'y'
                        if idx_top == -1:
                            raw_points_y.append(top)
                        idx_bottom = self.get_closest_idx(bottom, raw_points_y, bias)
                        if idx_bottom == -1:
                            raw_points_y.append(bottom)
                        fixed_x = (left + right) / 2.0
                        #fixed_x = int(fixed_x)
                        idx_fixed_x = self.get_closest_idx(fixed_x, raw_points_x, bias)
                        if idx_fixed_x >= 0:
                            fixed_x = raw_points_x[idx_fixed_x]
                        else:
                            raw_points_x.append(fixed_x)

                        pt1 = (fixed_x, top)
                        pt2 = (fixed_x, bottom)
                    # update data
                    if pt1 not in raw_points.keys():
                        raw_points[pt1] = []
                        points_visited[pt1] = False
                    if pt2 not in raw_points.keys():
                        raw_points[pt2] = []
                        points_visited[pt2] = False
                    tmp_idx_line = len(raw_lines)
                    if (pt1, pt2) not in raw_lines and (pt2, pt1) not in raw_lines:
                        raw_lines.append((pt1, pt2))
                        raw_points[pt1].append(tmp_idx_line)
                        raw_points[pt2].append(tmp_idx_line)
                else:  # a rectangle
                    if idx_left == -1:
                        raw_points_x.append(left)
                    idx_right = self.get_closest_idx(right, raw_points_x, bias)
                    if idx_right == -1:
                        raw_points_x.append(right)
                    if idx_top == -1:
                        raw_points_y.append(top)
                    idx_bottom = self.get_closest_idx(bottom, raw_points_y, bias)
                    if idx_bottom == -1:
                        raw_points_y.append(bottom)
                    pt1 = (left, top)
                    pt2 = (right, top)
                    pt3 = (right, bottom)
                    pt4 = (left, bottom)
                    points_visited[pt1] = False
                    points_visited[pt2] = False
                    points_visited[pt3] = False
                    points_visited[pt4] = False
                    if pt1 not in raw_points:
                        raw_points[pt1] = []
                    if pt2 not in raw_points:
                        raw_points[pt2] = []
                    if pt3 not in raw_points:
                        raw_points[pt3] = []
                    if pt4 not in raw_points:
                        raw_points[pt4] = []
                    # raw_lines.append( (pt1, pt2) )
                    tmp_idx_line = len(raw_lines)
                    if (pt1, pt2) not in raw_lines and (pt2, pt1) not in raw_lines:
                        raw_lines.append((pt1, pt2))
                        raw_points[pt1].append(tmp_idx_line)
                        raw_points[pt2].append(tmp_idx_line)
                    # raw_lines.append( (pt2, pt3) )
                    tmp_idx_line = len(raw_lines)
                    if (pt2, pt3) not in raw_lines and (pt3, pt2) not in raw_lines:
                        raw_lines.append((pt2, pt3))
                        raw_points[pt2].append(tmp_idx_line)
                        raw_points[pt3].append(tmp_idx_line)
                    # raw_lines.append( (pt3, pt4) )
                    tmp_idx_line = len(raw_lines)
                    if (pt3, pt4) not in raw_lines and (pt4, pt3) not in raw_lines:
                        raw_lines.append((pt3, pt4))
                        raw_points[pt3].append(tmp_idx_line)
                        raw_points[pt4].append(tmp_idx_line)
                    # raw_lines.append( (pt4, pt1) )
                    tmp_idx_line = len(raw_lines)
                    if (pt4, pt1) not in raw_lines and (pt1, pt4) not in raw_lines:
                        raw_lines.append((pt4, pt1))
                        raw_points[pt4].append(tmp_idx_line)
                        raw_points[pt1].append(tmp_idx_line)
        # print raw_lines
        # print raw_points
        # calculate the points included in a table, and the grids
        assert len(points_visited.keys()) == len(raw_points.keys()), "points amount and points list length do not match"
        return raw_lines, raw_points, points_visited

    def get_tables_init_info(self, raw_points, raw_lines, points_visited):
        '''Grouped Points and Lines'''
        point_list = raw_points.copy()

        def recursively_get_group(tmp_point):
            ret_val = []
            # if the point has already been visited
            if not points_visited[tmp_point]:
                points_visited[tmp_point] = True
                ret_val.append(tmp_point)
                # get the neighbours
                next_idx_lst = point_list.pop(tmp_point)
                for idx in next_idx_lst:
                    line = raw_lines[idx]
                    next_point = line[0]
                    if next_point == tmp_point:
                        next_point = line[1]
                    if points_visited[next_point]:
                        continue
                    next_list = recursively_get_group(next_point)
                    ret_val.extend(next_list)

            return ret_val

        table_list = []  # points in tables
        table_line_list = []  # lines that belong to a specific table
        divider_list = []  # the lines
        while len(point_list.keys()):
            next_starting_point = point_list.keys()[0]
            next_group = recursively_get_group(next_starting_point)
            if len(next_group) > 2:  # it is a table, not a line
                next_group.sort()
                table_list.append(next_group)
                divider_list.append([])
                table_line_list.append([])

        # get the lines' list
        for line in raw_lines:
            for i in range(len(table_list)):
                if line[0] in table_list[i] or line[1] in table_list[i]:
                    table_line_list[i].append(line)
                    break
        # print table_line_list
        return table_list, table_line_list, divider_list

    def get_tables_divider_list(self, table_list, table_line_list, divider_list, bias):
        # get the regularized lines
        for i in range(len(table_list)):
            print "table", i, len(table_list)
            tmp_xs = []
            tmp_ys = []
            tmp_table = table_list[i]
            tmp_lines = table_line_list[i]

            # print tmp_table
            for pt in tmp_table:
                pt_x = pt[0]
                pt_y = pt[1]
                if pt_x not in tmp_xs:
                    tmp_xs.append(pt_x)
                if pt_y not in tmp_ys:
                    tmp_ys.append(pt_y)
            tmp_xs.sort()
            tmp_ys.sort()
            # print tmp_xs
            # print tmp_ys
            # 规范一下xs和ys从而避免一个线段被分成两个的状况

            len_xs = len(tmp_xs)
            len_ys = len(tmp_ys)
            if len_xs < 2 or len_ys < 2:
                continue
            keep_xs = {}
            keep_ys = {}
            x_lines = {}  # x: [[y1, y2], [y1', y2']...], same x, vertical
            y_lines = {}  # y: [[x1, x2], [x1', x2']...], same y, horizontal
            keep_xs[tmp_xs[0]] = True
            keep_ys[tmp_ys[0]] = True
            keep_xs[tmp_xs[len_xs - 1]] = True
            keep_ys[tmp_ys[len_ys - 1]] = True

            for tmp_x in tmp_xs[1: len_xs - 1]:
                keep_xs[tmp_x] = False
            for tmp_y in tmp_ys[1: len_ys - 1]:
                keep_ys[tmp_y] = False

            for line in tmp_lines:
                # 找出合法的点
                pt1 = min(line[0], line[1])
                pt2 = max(line[0], line[1])
                if pt1[0] == pt2[0]:
                    # print "same x"
                    tmp_x = pt1[0]
                    tmp_y = [pt1[1], pt2[1]]
                    keep_xs[tmp_x] = True
                    if tmp_x in x_lines.keys():
                        # merge
                        # prev_tmp_y = copy.copy(tmp_y)
                        n_tmp_col_lines = len(x_lines[tmp_x])
                        for c in range(n_tmp_col_lines):
                            tmp_idx = n_tmp_col_lines - 1 - c
                            merged_line = self.line_merge(x_lines[tmp_x][tmp_idx], tmp_y, bias=bias)
                            if len(merged_line) == 1:
                                x_lines[tmp_x].pop(tmp_idx)
                                tmp_y[0] = merged_line[0][0]
                                tmp_y[1] = merged_line[0][1]
                        x_lines[tmp_x].append(tmp_y)
                    else:
                        x_lines[tmp_x] = [tmp_y]
                elif pt1[1] == pt2[1]:
                    # print "same y"
                    tmp_y = pt1[1]
                    tmp_x = [pt1[0], pt2[0]]
                    keep_ys[tmp_y] = True
                    if tmp_y in y_lines.keys():
                        # merge
                        n_tmp_row_lines = len(y_lines[tmp_y])
                        for r in range(n_tmp_row_lines):
                            tmp_idx = n_tmp_row_lines - 1 - r
                            merged_line = self.line_merge(y_lines[tmp_y][tmp_idx], tmp_x, bias=bias)
                            if len(merged_line) == 1:
                                y_lines[tmp_y].pop(tmp_idx)
                                tmp_x[0] = merged_line[0][0]
                                tmp_x[1] = merged_line[0][1]
                        y_lines[tmp_y].append(tmp_x)
                    else:
                        y_lines[tmp_y] = [tmp_x]
            tmp_xs = [k for k in keep_xs.keys() if keep_xs[k]]
            tmp_ys = [k for k in keep_ys.keys() if keep_ys[k]]
            tmp_xs.sort()
            tmp_ys.sort()
            # table list update!
            j = len(tmp_table) - 1
            while j >= 0:
                if tmp_table[j][0] not in tmp_xs or tmp_table[j][1] not in tmp_ys:
                    table_list[i].pop(j)
                j -= 1
            # line update
            tmp_lines = []

            for x_line_key in x_lines.keys():
                x_lines[x_line_key].sort()
                for x_line in x_lines[x_line_key]:
                    pt1 = (x_line_key, x_line[0])
                    pt2 = (x_line_key, x_line[1])
                    tmp_lines.append((pt1, pt2))
            for y_line_key in y_lines.keys():
                y_lines[y_line_key].sort()
                for y_line in y_lines[y_line_key]:
                    pt1 = (y_line[0], y_line_key)
                    pt2 = (y_line[1], y_line_key)
                    tmp_lines.append((pt1, pt2))
            # 处理分割线
            for line in tmp_lines:
                pt1 = min(line[0], line[1])
                pt2 = max(line[0], line[1])
                #if pt1[0] == pt2[0] and pt1[1] == pt2[1]:
                #    continue
                if pt1[0] == pt2[0]:  # same x
                    start_line_idx = -1
                    end_line_idx = -1
                    # print pt1, pt2
                    for idx in range(len(tmp_ys)):
                        if same(tmp_ys[idx], pt1[1]):
                            start_line_idx = idx
                        if same(tmp_ys[idx], pt2[1]):
                            end_line_idx = idx
                            break  # sorted
                    if start_line_idx == -1 or end_line_idx == -1:
                        pass
                    assert start_line_idx != -1 and end_line_idx != -1, "unrecorded point axis {0} or {1}, not recorded in {2}".format(
                        pt1[1], pt2[1], tmp_ys)
                    for idx in range(start_line_idx, end_line_idx):
                        tmp_pt1 = (pt1[0], tmp_ys[idx])
                        tmp_pt2 = (pt1[0], tmp_ys[idx + 1])
                        if (tmp_pt1, tmp_pt2) not in divider_list[i] and (tmp_pt2, tmp_pt1) not in divider_list[i]:
                            divider_list[i].append((tmp_pt1, tmp_pt2))
                elif pt1[1] == pt2[1]:  # same y
                    start_line_idx = -1
                    end_line_idx = -1
                    # print pt1, pt2
                    for idx in range(len(tmp_xs)):
                        if same(tmp_xs[idx], pt1[0]):
                            start_line_idx = idx
                        if same(tmp_xs[idx], pt2[0]):
                            end_line_idx = idx
                            break  # because it was sorted

                    assert start_line_idx != -1 and end_line_idx != -1, "error happend when building the frame of the table"
                    for idx in range(start_line_idx, end_line_idx):
                        tmp_pt1 = (tmp_xs[idx], pt1[1])
                        tmp_pt2 = (tmp_xs[idx + 1], pt1[1])
                        if (tmp_pt1, tmp_pt2) not in divider_list[i] and (tmp_pt2, tmp_pt1) not in divider_list[i]:
                            divider_list[i].append((tmp_pt1, tmp_pt2))
                else:
                    assert False, "seems that it is not a regular table"
            # print divider_list[i]
        return divider_list

    #################

    def get_tables(self, layout,text_cols):
        debug = self.debug_mode_on  # False #True
        # 在debug状态画出页码的边框
        if debug:
            page_range = {
                "left": layout.x0,
                "right": layout.x1,
                "top": layout.y1,
                "bottom": layout.y0
            }
            offset_x = -1.0 * (page_range["right"] + page_range["left"]) / 2.0
            offset_y = -1.0 * (page_range["top"] + page_range["bottom"]) / 2.0
            size_x = 1.5 * (page_range["right"] - page_range["left"])
            size_y = 1.5 * (page_range["top"] - page_range["bottom"])
            #draw = Draw(size_x, size_y, offset_x, offset_y)
           # draw.square(page_range["left"], page_range["right"], page_range["top"], page_range["bottom"])

        # step 1
        bias, table_outline_elem_lst, table_raw_dash_lst, dashline_parser_xs, dashline_parser_ys = \
            self.get_tables_elements(layout,text_cols)
        if UCC:
            self.show_page_layout_lines(layout, table_outline_elem_lst)
        # step 2
        table_dashlines = self.get_tables_dashlines(table_raw_dash_lst, bias)
        print table_dashlines

        for idx,dashline in enumerate(table_dashlines):
            print idx
            if dashline['x0'] not in dashline_parser_xs:
                dashline_parser_xs.append(dashline['x0'])
            if dashline['x1'] not in dashline_parser_xs:
                dashline_parser_xs.append(dashline['x1'])
            if dashline['y0'] not in dashline_parser_ys:
                dashline_parser_ys.append(dashline['y0'])
            if dashline['y1'] not in dashline_parser_ys:
                dashline_parser_ys.append(dashline['y1'])
        dashline_parser_xs.sort()
        dashline_parser_ys.sort()



        table_outline_elem_lst = self.get_tables_elements_all(table_outline_elem_lst, table_dashlines,
                                                              dashline_parser_xs, dashline_parser_ys)
        # step 3: 粗略分出不同表格的子区域
        clean_tables_lst = self.get_tables_areas(table_outline_elem_lst, bias)

        # Step 4: 然后规范一下坐标值
        # 开始整理表格内容
        print "number of potential tables in this page is {0}".format(len(clean_tables_lst))
        #self.show_page_layout(layout)

        try:
            raw_lines, raw_points, points_visited = self.get_tables_raw_frame(clean_tables_lst, bias)
        except Exception:
            pass

        if debug:
            point_list = raw_points.copy()
            def debug_walk(tmp_point):
                if points_visited[tmp_point]:
                    return
                points_visited[tmp_point] = True
                draw.dot(tmp_point[0], tmp_point[1], size=15, color_string="green")
                next_links = point_list[tmp_point]
                for idx in next_links:
                    line = raw_lines[idx]
                    debug_walk(line[0])
                    debug_walk(line[1])
            test_point = point_list.keys()[0]
            test_value = point_list[test_point]
            debug_walk(test_point)
            print "debug walk done"
        #self.show_page_layout_lines(layout, raw_lines)

        # step 5

        #self.show_page_layout_points(layout, raw_points)
        table_list, table_line_list, divider_list = self.get_tables_init_info(raw_points, raw_lines, points_visited)

        print len(divider_list)
        #

        # step 6
        divider_list = self.get_tables_divider_list(table_list, table_line_list, divider_list, bias)
        #self.show_page_layout_post(layout, divider_list)
        # test


        if debug:
            for table in table_list:
                for pt in table:
                     draw.dot(pt[0], pt[1], size=10, color_string="red")
                 # raw_input()
            for table in table_list:
                n_pts = len(table)
                draw.dot(table[0][0], table[0][1], size=10, color_string="red")
                draw.dot(table[n_pts - 1][0], table[n_pts - 1][1], size=10, color_string="red")
            for line in raw_lines:
                draw.line(line[0][0], line[0][1], line[1][0], line[1][1])


        if debug:
            # debug
            for lst in divider_list:
                print len(lst)
                for divider in lst:
                    print divider
                    start = divider[0]
                    end = divider[1]
                    draw.set_color("red")
                    # print start[0], start[1], end[0], end[1]
                    draw.line(start[0], start[1], end[0], end[1])


        if debug:
            raw_input()

        # print "the number of tables we detected is {0}".format(len(table_list))

        return table_list, bias, divider_list

    def get_table_frame(self, table_points_list, bias, table_divider_list):
        ret_val = TableFrame(table_points_list, bias, table_divider_list)
        return ret_val

    def add_cross_point(self, lines, points):

        local_lines = copy.copy(lines)
        tables = []
        #get tables
        while len(local_lines) > 0:
            top_y = 0
            table = []
            top_id = -1
            for i in range(len(local_lines)):
                l = local_lines[i]
                if l[0][1] == l[1][1]: #水平线
                    if l[0][1] > top_y:
                        top_y = l[0][1]
                        top_id = i
            bottom_y = top_y
            for j in range(len(local_lines)):
                l = local_lines[j]
                if l[0][0] == l[1][0]:  # 垂直线
                    #print max(l[0][1],l[1][1]),top_y,l
                    if same(top_y , max(l[0][1],l[1][1])):
                        if min(l[0][1],l[1][1]) < bottom_y:
                            bottom_y = min(l[0][1],l[1][1])
            if bottom_y == top_y:
                del local_lines[top_id]  # 移除页眉的线
                continue
            for k in range(len(local_lines)-1, -1, -1):
                l = local_lines[k]
                if min(l[0][1],l[1][1]) > bottom_y-1 and  max(l[0][1],l[1][1]) <top_y+1:
                    table.append(l)
                    del local_lines[k]

            tables.append(table)

        segs = []
        for idx,t_lines in enumerate(tables):
            x_lines = []
            y_lines = []
            points_od = {}
            x_seg_points = {}
            y_seg_points = {}
            for l in t_lines:
                if l[0][1] == l[1][1]:
                    x_lines.append(l)
                elif l[0][0] == l[1][0]:
                    y_lines.append(l)

            #找出最左，最右的垂直线

            left = 10000
            right = 0
            left_points = []
            right_points = []
            for x_l in x_lines:
                min_x = min(x_l[0][0], x_l[1][0])
                max_x = max(x_l[0][0], x_l[1][0])
                left = min(min_x, left)
                right = max(max_x, right)
                for y_l in y_lines:
                    k = (y_l[0][0],x_l[0][1])
                    # y_line
                    min_y = min(y_l[0][1], y_l[1][1])
                    max_y = max(y_l[0][1], y_l[1][1])
                    # x_line

                    if  (k[0] > min_x-1 and k[0]<max_x+1) and (k[1]>min_y-1 and k[1]<max_y +1):
                        points_od[k] = [0]
                y0 = x_l[0][1]
                left_points.append([min_x,y0])
                right_points.append([max_x,y0])

            if left is not 10000:
                for p in left_points:
                    points_od[(left,p[1])] = [0]
            if right is not 0:
                for p in right_points:
                    points_od[(right,p[1])]= [0]




            for k in points_od:
                if k[1] not in x_seg_points:
                    x_seg_points[k[1]] = []
                x_seg_points[k[1]].append(k[0])
            for y in x_seg_points:
                x_seg_points[y].sort()
                last_x= x_seg_points[y][0]
                for i in range(1,len(x_seg_points[y])):
                    segs.append([(last_x,y),(x_seg_points[y][i],y)])
                    last_x = x_seg_points[y][i]


            for k in points_od:
                if k[0] not in y_seg_points:
                    y_seg_points[k[0]] = []
                y_seg_points[k[0]].append(k[1])

            for x in y_seg_points:
                y_seg_points[x].sort()
                last_y = y_seg_points[x][0]
                for i in range(1, len(y_seg_points[x])):
                    segs.append([(x, last_y), (x, y_seg_points[x][i])])
                    last_y = y_seg_points[x][i]
        #print len(segs)
        return segs


class TableFrame(object):
    def __init__(self, table_points_list, bias, table_divider_list):
        # assert len(table_points_list) > 2, "the data passed in is not a table at all"
        self.bias = bias
        self.grids = {"x": [], "y": []}
        self.data = []  # content, [['XXX', 'XXX'],['XXX', 'XXX']...]
        self.font = []
        self.rowspan = []
        self.colspan = []
        self.location_map = {}  # content: [(x_location, y_location): (x_data, y_data)]
        self.range = {"max_x": -1, "max_y": -1, "min_x": 0, "min_y": 0}
        for point in table_points_list:
            x = point[0]
            y = point[1]
            if x not in self.grids['x']:
                self.grids['x'].append(x)
            if y not in self.grids['y']:
                self.grids['y'].append(y)
        self.grids['x'].sort()
        self.grids['y'].sort(reverse=True)
        # print self.grids['x']
        # print self.grids['y']
        # assert len(self.grids['x']) > 1 and len(self.grids['y']) > 1, "the table data does not represent an area"
        #两个点确定一个单元格？ 处于同一条线上的不行
        if len(table_points_list) <= 2 or len(self.grids['x']) <= 1 or len(self.grids['y']) <= 1:
            self.grids = None
        else:
            # get the structure of the table
            # print table_divider_list
            n_rows = len(self.grids['y']) - 1
            n_cols = len(self.grids['x']) - 1
            for i in range(n_rows):
                empty_line = []
                empty_font = []
                empty_rowspan = []
                empty_colspan = []
                tmp_col = 0
                for j in range(n_cols):
                    # print "up, down, left, right"
                    # print self.grids['y'][i], self.grids['y'][i + 1], self.grids['x'][j], self.grids['x'][j + 1]
                    upperleft_corner = (self.grids['x'][j], self.grids['y'][i])
                    lowerleft_corner = (self.grids['x'][j], self.grids['y'][i + 1])
                    upperright_corner = (self.grids['x'][j + 1], self.grids['y'][i])
                    lowerright_corner = (self.grids['x'][j + 1], self.grids['y'][i + 1])
                    upper_connected = False
                    left_connected = False

                    if i > 0:
                        # possible that rowspan > 0
                        if (upperleft_corner, upperright_corner) not in table_divider_list and \
                                        (upperright_corner, upperleft_corner) not in table_divider_list:
                            # connected to the upper grid
                            upper_connected = True
                    if j > 0:
                        # possible that colspan > 0
                        if (lowerleft_corner, upperleft_corner) not in table_divider_list and \
                                        (upperleft_corner, lowerleft_corner) not in table_divider_list:
                            # connected to the left grid
                            left_connected = True

                    # print i, j, upper_connected, left_connected

                    # upper_connected = False
                    # left_connected = False
                    # print "point({2},{3}) upper_connected={0}, left_connected={1}".format(upper_connected, left_connected, i, j)
                    '''if i == 2 and j == 1:
                        print upper_connected
                        print (upperleft_corner, upperright_corner)
                        print (upperright_corner, upperleft_corner)
                        table_divider_list.sort()
                        print table_divider_list
                        print n_cols, n_rows
                        print self.grids['y']
                        '''

                    if upper_connected and left_connected:
                        self.location_map[(i, j)] = self.location_map[(i - 1, j)]
                    elif upper_connected:
                        self.location_map[(i, j)] = self.location_map[(i - 1, j)]
                        # print "self.location_map[({0}, {1})] = ({2}, {3})".format(i, j, self.location_map[i-1, j][0], self.location_map[i-1, j][1])
                        representer_i = self.location_map[(i - 1, j)][0]
                        representer_j = self.location_map[(i - 1, j)][1]
                        self.rowspan[representer_i][representer_j] += 1

                    elif left_connected:
                        self.location_map[(i, j)] = self.location_map[i, (j - 1)]
                        # print "self.location_map[({0}, {1})] = ({2}, {3})".format(i, j, self.location_map[i, (j - 1)][0], self.location_map[i, (j - 1)][1])
                        representer_i = self.location_map[(i, j - 1)][0]
                        representer_j = self.location_map[(i, j - 1)][1]
                        # self.colspan[representer_i][representer_j] += 1
                        '''
                        print len(empty_colspan)
                        print representer_j
                        print i, j, tmp_col
                        print empty_colspan
                        # '''
                        empty_colspan[representer_j] += 1

                    else:  # the starting grid of an area
                        empty_line.append([])
                        empty_font.append(None)
                        empty_rowspan.append(1)
                        empty_colspan.append(1)
                        # print "self.location_map[({0}, {1})] = ({2}, {3})".format(i, j, i, tmp_col)
                        self.location_map[(i, j)] = (i, tmp_col)
                        tmp_col += 1
                # print "empty colspan"
                # print empty_colspan
                self.data.append(empty_line)
                self.font.append(empty_font)
                self.rowspan.append(empty_rowspan)
                self.colspan.append(empty_colspan)
            # print self.rowspan
            # print self.colspan
            corner1 = table_points_list[0]
            corner2 = table_points_list[len(table_points_list) - 1]
            self.range['max_x'] = max(corner1[0], corner2[0])
            self.range['max_y'] = max(corner1[1], corner2[1])
            self.range['min_x'] = min(corner1[0], corner2[0])
            self.range['min_y'] = min(corner1[1], corner2[1])

    def locate(self, point):
        def greater_than(a, b):
            if a + self.bias > b:
                return True
            return False

        def smaller_than(a, b):
            if a < b + self.bias:
                return True
            return False

        # point: (x, y)
        x = point[0]
        y = point[1]
        x_idx = -1
        y_idx = -1
        n_x = len(self.grids['x'])
        n_y = len(self.grids['y'])
        # print n_x, n_y
        # print self.grids['x']
        # print self.grids['y']
        for i in range(1, n_x):
            # print "compare {0} with {1} and {2}".format(x, self.grids['x'][i - 1], self.grids['x'][i])
            if greater_than(x, self.grids['x'][i - 1]) and smaller_than(x, self.grids['x'][i]):
                x_idx = i - 1
                break
        for i in range(1, n_y):
            # print "compare {0} with {1} and {2}".format(y, self.grids['y'][i - 1], self.grids['y'][i])
            if smaller_than(y, self.grids['y'][i - 1]) and greater_than(y, self.grids['y'][i]):
                y_idx = i - 1
                break
        # print x_idx, y_idx
        if x_idx == -1 or y_idx == -1:
            return None
        (row, col) = self.location_map[(y_idx, x_idx)]
        return (row, col)  # row, col

    def get_clean_data(self):
        clean_data = []
        clean_fonts = []
        clean_rowspan = []
        clean_colspan = []
        for i in range(len(self.data)):
            line = self.data[i]
            empty = True
            for elem in line:
                if len(elem):
                    empty = False
                    break
            if not empty:
                clean_data.append(copy.copy(line))
                clean_fonts.append(copy.copy(self.font[i]))
                clean_rowspan.append(copy.copy(self.rowspan[i]))
                clean_colspan.append(copy.copy(self.colspan[i]))
        return clean_data, clean_fonts, clean_rowspan, clean_colspan

    def is_in_range(self, point):
        def greater_than(a, b):
            if a + self.bias > b:
                return True
            return False

        def smaller_than(a, b):
            if a < b + self.bias:
                return True
            return False

        # point: (x, y)
        x = point[0]
        y = point[1]
        x_idx = -1
        if greater_than(x, self.range['min_x']) and smaller_than(x, self.range['max_x']) \
                and greater_than(y, self.range['min_y']) and smaller_than(y, self.range['max_y']):
            return True
        return False

    def add_data(self, location, content):
        row = location[0]
        col = location[1]
        self.data[row][col].append(content)

    def included_in_table(self, another_table):
        corner1 = (self.range['min_x'], self.range['min_y'])
        corner2 = (self.range['max_x'], self.range['min_y'])
        return another_table.is_in_range(corner1) and another_table.is_in_range(corner2)


class Draw(object):
    def __init__(self, size_x, size_y, offset_x, offset_y):
        self.offset_x = offset_x
        self.offset_y = offset_y
        turtle.clear()
        turtle.speed(0)
        turtle.screensize(canvwidth=size_x, canvheight=size_y, bg=None)
    def done(self):
        turtle.done()
    def set_color(self, color_string):
        turtle.pencolor(color_string)

    def dot(self, x, y, size=3, color_string="purple"):
        # turtle.penup()
        turtle.goto(x + self.offset_x, y + self.offset_y)
        # turtle.pendown()
        turtle.dot(size, color_string)

    # turtle.penup()
    def line(self, start_x, start_y, end_x, end_y):
        turtle.penup()
        turtle.goto(start_x + self.offset_x, start_y + self.offset_y)
        turtle.pendown()
        self.dot(start_x, start_y)
        turtle.goto(end_x + self.offset_x, end_y + self.offset_y)
        turtle.penup()

    def square(self, left, right, top, bottom):
        turtle.penup()
        turtle.goto(left + self.offset_x, top + self.offset_y)
        turtle.pendown()
        turtle.goto(right + self.offset_x, top + self.offset_y)
        turtle.goto(right + self.offset_x, bottom + self.offset_y)
        turtle.goto(left + self.offset_x, bottom + self.offset_y)
        turtle.goto(left + self.offset_x, top + self.offset_y)
        turtle.penup()

