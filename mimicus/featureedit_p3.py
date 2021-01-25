'''
Copyright 2012-2014 Nedim Srndic, University of Tuebingen

This file is part of Mimicus.

Mimicus is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

Mimicus is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with Mimicus.  If not, see <http://www.gnu.org/licenses/>.
##############################################################################
featureedit.py

Feature modification method.

Created on October 22, 2012.
'''

"""
This is a python3 porting of the original featureedit.py code.
With the intention of keeping the results as identical as possible
to the original, no speed or stylistic modification has been
added, and only the bare minimum changes necessary to make it
work have been performed.
"""

import calendar
import copy
import dateutil.parser
import mmap
import numpy
import operator
import os
import re
import subprocess
import sys
import tempfile
import time
import traceback

# New
import hashlib


class CachedMethod(object):
    '''
    Used as a custom class method decorator to calculate the return 
    value of a function once and than cache it for subsequent 
    retrieval. 
    '''
    def __init__(self, calculate_function):
        self._calculate = calculate_function

    def __get__(self, obj, _=None):
        attr_name = '_{}_attr'.format(self._calculate.__name__)
        if hasattr(obj, attr_name):
            return getattr(obj, attr_name)
        value = self._calculate(obj)
        setattr(obj, attr_name, lambda: value)
        return lambda: value

class FeatureEditError(Exception):
    '''
    A class representing an exception when reading or modifying features 
    using the FeatureEdit class. All exceptions in this module are 
    derived from this class. 
    '''
    def __init__(self, message, *args, **kwargs):
        self.message = message
        Exception.__init__(self, *args, **kwargs)
    
    def __str__(self):
        return self.message

class ReadOnlyFeatureError(FeatureEditError):
    '''
    A class representing an exception when trying to modify a feature 
    which is read-only. 
    '''
    def __init__(self, message, *args, **kwargs):
        self.message = message
        FeatureEditError.__init__(self, message, *args, **kwargs)
    
    def __str__(self):
        return self.message

class MinimumExceededError(FeatureEditError):
    '''
    A class representing an exception when attempting to set a too 
    low value for a feature. 
    '''
    def __init__(self, message, *args, **kwargs):
        self.message = message
        FeatureEditError.__init__(self, message, *args, **kwargs)
    
    def __str__(self):
        return self.message

class MaximumExceededError(FeatureEditError):
    '''
    A class representing an exception when attempting to set a too 
    high value for a feature. 
    '''
    def __init__(self, message, *args, **kwargs):
        self.message = message
        FeatureEditError.__init__(self, message, *args, **kwargs)
    
    def __str__(self):
        return self.message

def _perl_regex(regex, infile):
    '''
    Runs a child perl process on a given file evaluating the given regex and 
    returns the standard output as a string.
    '''
    perl = subprocess.Popen(['perl', '-ln0777e', regex, infile], stdout=subprocess.PIPE)
    (stdoutdata, stderrdata) = perl.communicate()
    if stderrdata is not None and len(stderrdata) > 0:
        sys.stderr.write('Child (perl) error: %s\n' % stderrdata)
        raise
    else:
        return stdoutdata

# Regular expressions precompiled for speed
_regex_pdf_box = re.compile(r'\d\s+([+|-]?(?:\d+\.?\d*|\d*\.?\d+))\s+([+|-]?(?:\d+\.?\d*|\d*\.?\d+))\s+([+|-]?(?:\d+\.?\d*|\d*\.?\d+))\s+([+|-]?(?:\d+\.?\d*|\d*\.?\d+))')
_regex_pdf_image_height = re.compile(r'.*\/Height(?:\s|\n)+(\d+).*')
_regex_pdf_image_width = re.compile(r'.*\/Width(?:\s|\n)+(\d+).*')

# Original
# _regex_pdf_version = re.compile(r'%PDF-1\.(\d)')
# New
_regex_pdf_version = re.compile(b'%PDF-1\.(\d)')

# Features which are simple to increment
_incrementable_feats = {'count_acroform' : '/AcroForm', 
                'count_acroform_obs' : '/Acro#46orm', 
                'count_action' : '/AA', 
                'count_action_obs' : '/Open#41ction', 
                'count_box_a4' : '[0 0 597 842]', 
                'count_box_legal' : '[0 0 611 1007]', 
                'count_box_letter' : '[0 0 611 791]', 
                'count_box_other' : '[33 34 35 36]', 
                'count_box_overlap' : '[0 0 597 791]', 
                'count_endobj' : 'endobj', 
                'count_endstream' : 'endstream', 
                'count_eof' : '%EOF', 
                'count_font' : '/Font', 
                'count_font_obs' : '/F#6fnt', 
                'count_image_large' : '<< /Height 888/Width 888>>', 
                'count_image_med' : '<< /Height 255/Width 255>>', 
                'count_image_small' : '<< /Height 65/Width 65>>', 
#                'count_image_total', 
                'count_image_xlarge' : '<< /Height 8888/Width 8888>>', 
                'count_image_xsmall' : '<< /Height 1/Width 1>>', 
                'count_javascript' : '/JavaScript', 
                'count_javascript_obs' : '/Jav#61Script', 
                'count_js' : '/JS', 
                'count_js_obs' : '/#4AS', 
                'count_obj' : '22 0 obj', 
                'count_objstm' : '/ObjStm', 
                'count_objstm_obs' : '/Ob#6aStm', 
                'count_page' : '/Page', 
                'count_page_obs' : '/#50age', 
                'count_startxref' : 'startxref', 
                'count_stream' : 'stream', 
#                'count_stream_diff', 
                'count_trailer' : 'trailer', 
                'count_xref' : 'xref'}

# Metadata features
_metadata_feats = {'author' : ' /Author({})\n', 
                    'creator' : ' /Creator({})\n', 
                    'keywords' : ' /Keywords({})\n', 
                    'producer' : ' /Producer({})\n', 
                    'subject' : ' /Subject({})\n', 
                    'title' : ' /Title({})\n'}

def _sanitize_PDF_literal_string(pdfstr):
    # Orignal
    # pdfstr = pdfstr.replace(r'\n', '\n').replace(r'\r', '\r').replace(r'\t', '\t').replace(r'\b', '\b').replace(r'\f', '\f').replace(r'\(', '(').replace(r'\)', ')').replace(r'\\', '\\')
    # pdfstr = pdfstr.replace('\\\n', '').replace('\r\n', '\n').replace('\r', '\n')
    # New
    pdfstr = pdfstr.replace(b'\n', b'\n').replace(b'\r', b'\r').replace(b'\t', b'\t').replace(b'\b', b'\b').replace(b'\f', b'\f').replace(b'\(', b'(').replace(b'\)', b')').replace(b'\\', b'\\')
    pdfstr = pdfstr.replace(b'\\\n', b'').replace(b'\r\n', b'\n').replace(b'\r', b'\n')
    return pdfstr

class FileDefined:
    '''
    A class used as a marker for feature descriptions indicating that the 
    range of valid values for that feature (its minimum, maximum or both) 
    is bounded by its concrete value in a concrete file. For example, if the 
    FileDefined type is used as the lower bound of a valid range of a feature, 
    then this file already has the minimum value of this feature, i.e., it 
    cannot be reduced further. 
    '''

'''
For every feature, a dictionary is defined describing that feature:
its type ('type'), whether it may be altered or not ('edit', with the 
values 'y' if altering is implemented, 'n' if it's impossible to 
alter and 'm' if altering is not directly implemented, but the 
feature value might change by modifying some other features) and 
the range ('range') within which it may be altered as a tuple of 
lower and upper bound (FileDefined means that this lower or upper 
bound cannot be modified further than what is currently in the file). 
The range represents actual minimum and maximum values seen in the 
Contagio dataset. 
'''
_pdfrate_feature_descriptions = {
                'author_dot'              :{'type':int, 'range':(0, 24), 'edit':'y'},
                'author_lc'               :{'type':int, 'range':(0, 158), 'edit':'y'},
                'author_len'              :{'type':int, 'range':(0, 288), 'edit':'m'},
                'author_mismatch'         :{'type':int, 'range':(FileDefined, 45), 'edit':'m'},
                'author_num'              :{'type':int, 'range':(0, 63), 'edit':'y'},
                'author_oth'              :{'type':int, 'range':(0, 79), 'edit':'y'},
                'author_uc'               :{'type':int, 'range':(0, 108), 'edit':'y'},
                'box_nonother_types'      :{'type':int, 'range':(FileDefined, 2684), 'edit':'y'},
                'box_other_only'          :{'type':bool, 'range': (False, True), 'edit':'m'},
                'company_mismatch'        :{'type':int, 'range':(FileDefined, 2), 'edit':'m'},
                'count_acroform'          :{'type':int, 'range':(FileDefined, 7), 'edit':'y'},
                'count_acroform_obs'      :{'type':int, 'range':(FileDefined, 1), 'edit':'y'},
                'count_action'            :{'type':int, 'range':(FileDefined, 815), 'edit':'y'},
                'count_action_obs'        :{'type':int, 'range':(FileDefined, 1), 'edit':'y'},
                'count_box_a4'            :{'type':int, 'range':(FileDefined, 34), 'edit':'y'},
                'count_box_legal'         :{'type':int, 'range':(FileDefined, 268), 'edit':'y'},
                'count_box_letter'        :{'type':int, 'range':(FileDefined, 2684), 'edit':'y'},
                'count_box_other'         :{'type':int, 'range':(FileDefined, 12916), 'edit':'y'},
                'count_box_overlap'       :{'type':int, 'range':(FileDefined, 10), 'edit':'y'},
                'count_endobj'            :{'type':int, 'range':(FileDefined, 19632), 'edit':'y'},
                'count_endstream'         :{'type':int, 'range':(FileDefined, 6668), 'edit':'y'},
                'count_eof'               :{'type':int, 'range':(FileDefined, 24), 'edit':'y'},
                'count_font'              :{'type':int, 'range':(FileDefined, 7333), 'edit':'y'},
                'count_font_obs'          :{'type':int, 'range':(FileDefined, 5), 'edit':'y'},
                'count_image_large'       :{'type':int, 'range':(FileDefined, 35), 'edit':'y'},
                'count_image_med'         :{'type':int, 'range':(FileDefined, 278), 'edit':'y'},
                'count_image_small'       :{'type':int, 'range':(FileDefined, 311), 'edit':'y'},
                'count_image_total'       :{'type':int, 'range':(FileDefined, 4542), 'edit':'n'},
                'count_image_xlarge'      :{'type':int, 'range':(FileDefined, 3), 'edit':'y'},
                'count_image_xsmall'      :{'type':int, 'range':(FileDefined, 4525), 'edit':'y'},
                'count_javascript'        :{'type':int, 'range':(FileDefined, 404), 'edit':'y'},
                'count_javascript_obs'    :{'type':int, 'range':(FileDefined, 2), 'edit':'y'},
                'count_js'                :{'type':int, 'range':(FileDefined, 404), 'edit':'y'},
                'count_js_obs'            :{'type':int, 'range':(FileDefined, 2), 'edit':'y'},
                'count_obj'               :{'type':int, 'range':(FileDefined, 19632), 'edit':'y'},
                'count_objstm'            :{'type':int, 'range':(FileDefined, 1036), 'edit':'y'},
                'count_objstm_obs'        :{'type':int, 'range':(FileDefined, 1), 'edit':'y'},
                'count_page'              :{'type':int, 'range':(FileDefined, 1341), 'edit':'y'},
                'count_page_obs'          :{'type':int, 'range':(FileDefined, 6), 'edit':'y'},
                'count_startxref'         :{'type':int, 'range':(FileDefined, 24), 'edit':'y'},
                'count_stream'            :{'type':int, 'range':(FileDefined, 6668), 'edit':'y'},
                'count_stream_diff'       :{'type':int, 'range':(-2, 69), 'edit':'m'},
                'count_trailer'           :{'type':int, 'range':(FileDefined, 46), 'edit':'y'},
                'count_xref'              :{'type':int, 'range':(FileDefined, 46), 'edit':'y'},
                'createdate_dot'          :{'type':int, 'range':(0, 1), 'edit':'n'},
                'createdate_mismatch'     :{'type':int, 'range':(FileDefined, 92), 'edit':'m'},
                'createdate_ts'           :{'type':int, 'range':(0, 2058951292), 'edit':'y'},
                'createdate_tz'           :{'type':int, 'range':(-36000, 46800), 'edit':'y'},
                'createdate_version_ratio':{'type':float, 'range':(-1.0, 7326.0), 'edit':'m'},
                'creator_dot'             :{'type':int, 'range':(0, 5), 'edit':'y'},
                'creator_lc'              :{'type':int, 'range':(0, 46), 'edit':'y'},
                'creator_len'             :{'type':int, 'range':(0, 166), 'edit':'m'},
                'creator_mismatch'        :{'type':int, 'range':(FileDefined, 45), 'edit':'m'},
                'creator_num'             :{'type':int, 'range':(0, 105), 'edit':'y'},
                'creator_oth'             :{'type':int, 'range':(0, 64), 'edit':'y'},
                'creator_uc'              :{'type':int, 'range':(0, 31), 'edit':'y'},
                'delta_ts'                :{'type':int, 'range':(-1279940312, 1294753248), 'edit':'n'},
                'delta_tz'                :{'type':int, 'range':(-57600, 46800), 'edit':'n'},
                'image_mismatch'          :{'type':int, 'range':(FileDefined, 207), 'edit':'m'},
                'image_totalpx'           :{'type':int, 'range':(FileDefined, 119549960), 'edit':'m'},
                'keywords_dot'            :{'type':int, 'range':(0, 5), 'edit':'y'},
                'keywords_lc'             :{'type':int, 'range':(0, 291), 'edit':'y'},
                'keywords_len'            :{'type':int, 'range':(0, 446), 'edit':'m'},
                'keywords_mismatch'       :{'type':int, 'range':(FileDefined, 19), 'edit':'m'},
                'keywords_num'            :{'type':int, 'range':(0, 102), 'edit':'y'},
                'keywords_oth'            :{'type':int, 'range':(0, 185), 'edit':'y'},
                'keywords_uc'             :{'type':int, 'range':(0, 164), 'edit':'y'},
                'len_obj_avg'             :{'type':float, 'range':(0.1, 382922.0), 'edit':'m'},
                'len_obj_max'             :{'type':int, 'range':(FileDefined, 4161352), 'edit':'m'},
                'len_obj_min'             :{'type':int, 'range':(6, FileDefined), 'edit':'m'},
                'len_stream_avg'          :{'type':float, 'range':(0.0, 1531433.0), 'edit':'m'},
                'len_stream_max'          :{'type':int, 'range':(FileDefined, 4610074), 'edit':'m'},
                'len_stream_min'          :{'type':int, 'range':(0, FileDefined), 'edit':'m'},
                'moddate_dot'             :{'type':int, 'range':(0, 1), 'edit':'n'},
                'moddate_mismatch'        :{'type':int, 'range':(FileDefined, 23), 'edit':'m'},
                'moddate_ts'              :{'type':int, 'range':(0, 2058951292), 'edit':'y'},
                'moddate_tz'              :{'type':int, 'range':(-36000, 46800), 'edit':'y'},
                'moddate_version_ratio'   :{'type':float, 'range':(0.1, 7390.0), 'edit':'m'},
                'pdfid0_dot'              :{'type':int, 'range':(0, 1), 'edit':'m'},
                'pdfid0_lc'               :{'type':int, 'range':(0, 21), 'edit':'m'},
                'pdfid0_len'              :{'type':int, 'range':(0, 46), 'edit':'m'},
                'pdfid0_mismatch'         :{'type':int, 'range':(FileDefined, 3), 'edit':'m'},
                'pdfid0_num'              :{'type':int, 'range':(0, 44), 'edit':'m'},
                'pdfid0_oth'              :{'type':int, 'range':(0, 1), 'edit':'m'},
                'pdfid0_uc'               :{'type':int, 'range':(0, 21), 'edit':'m'},
                'pdfid1_dot'              :{'type':int, 'range':(0, 1), 'edit':'m'},
                'pdfid1_lc'               :{'type':int, 'range':(0, 21), 'edit':'m'},
                'pdfid1_len'              :{'type':int, 'range':(0, 32), 'edit':'m'},
                'pdfid1_mismatch'         :{'type':int, 'range':(FileDefined, 23), 'edit':'m'},
                'pdfid1_num'              :{'type':int, 'range':(0, 32), 'edit':'m'},
                'pdfid1_oth'              :{'type':int, 'range':(0, 1), 'edit':'m'},
                'pdfid1_uc'               :{'type':int, 'range':(0, 22), 'edit':'m'},
                'pdfid_mismatch'          :{'type':bool, 'range': (False, True), 'edit':'m'},
                'pos_acroform_avg'        :{'type':float, 'range':(FileDefined, 1.0), 'edit':'m'},
                'pos_acroform_max'        :{'type':float, 'range':(FileDefined, 1.0), 'edit':'m'},
                'pos_acroform_min'        :{'type':float, 'range':(0.0, 1,0), 'edit':'m'},
                'pos_box_avg'             :{'type':float, 'range':(FileDefined, 1.0), 'edit':'m'},
                'pos_box_max'             :{'type':float, 'range':(FileDefined, 1.0), 'edit':'m'},
                'pos_box_min'             :{'type':float, 'range':(0.0, 1.0), 'edit':'n'},
                'pos_eof_avg'             :{'type':float, 'range':(FileDefined, 1.0), 'edit':'m'},
                'pos_eof_max'             :{'type':float, 'range':(FileDefined, 1.0), 'edit':'n'},
                'pos_eof_min'             :{'type':float, 'range':(0.0, FileDefined), 'edit':'m'},
                'pos_image_avg'           :{'type':float, 'range':(FileDefined, 1.0), 'edit':'m'},
                'pos_image_max'           :{'type':float, 'range':(FileDefined, 1.0), 'edit':'m'},
                'pos_image_min'           :{'type':float, 'range':(0.0, 1.0), 'edit':'m'},
                'pos_page_avg'            :{'type':float, 'range':(FileDefined, 1.0), 'edit':'m'},
                'pos_page_max'            :{'type':float, 'range':(FileDefined, 1.0), 'edit':'m'},
                'pos_page_min'            :{'type':float, 'range':(0.0, 1.0), 'edit':'m'},
                'producer_dot'            :{'type':int, 'range':(0, 1962), 'edit':'y'},
                'producer_lc'             :{'type':int, 'range':(0, 7343), 'edit':'y'},
                'producer_len'            :{'type':int, 'range':(0, 32566), 'edit':'m'},
                'producer_mismatch'       :{'type':int, 'range':(FileDefined, 9), 'edit':'m'},
                'producer_num'            :{'type':int, 'range':(0, 25302), 'edit':'y'},
                'producer_oth'            :{'type':int, 'range':(0, 9233), 'edit':'y'},
                'producer_uc'             :{'type':int, 'range':(0, 13), 'edit':'y'},
                'ratio_imagepx_size'      :{'type':float, 'range':(0.0, 559.0), 'edit':'m'},
                'ratio_size_obj'          :{'type':float, 'range':(24.0, 382971.0), 'edit':'m'},
                'ratio_size_page'         :{'type':float, 'range':(266.0, 1.15e+13), 'edit':'m'},
                'ratio_size_stream'       :{'type':float, 'range':(316.0, 39680000000.0), 'edit':'m'},
                'size'                    :{'type':int, 'range':(FileDefined, 10000000), 'edit':'y'},
                'subject_dot'             :{'type':int, 'range':(0, 5), 'edit':'y'},
                'subject_lc'              :{'type':int, 'range':(0, 256), 'edit':'y'},
                'subject_len'             :{'type':int, 'range':(0, 413), 'edit':'m'},
                'subject_mismatch'        :{'type':int, 'range':(FileDefined, 15), 'edit':'m'},
                'subject_num'             :{'type':int, 'range':(0, 113), 'edit':'y'},
                'subject_oth'             :{'type':int, 'range':(0, 82), 'edit':'y'},
                'subject_uc'              :{'type':int, 'range':(0, 94), 'edit':'y'},
                'title_dot'               :{'type':int, 'range':(0, 11), 'edit':'y'},
                'title_lc'                :{'type':int, 'range':(0, 183), 'edit':'y'},
                'title_len'               :{'type':int, 'range':(0, 698), 'edit':'m'},
                'title_mismatch'          :{'type':int, 'range':(FileDefined, 517), 'edit':'m'},
                'title_num'               :{'type':int, 'range':(0, 420), 'edit':'y'},
                'title_oth'               :{'type':int, 'range':(0, 160), 'edit':'y'},
                'title_uc'                :{'type':int, 'range':(0, 74), 'edit':'y'},
                'version'                 :{'type':int, 'range':(1, 8), 'edit':'y'}}

'''
A sorted list of feature names.
'''
_pdfrate_feature_names = sorted(_pdfrate_feature_descriptions.keys())

class FeatureDescriptor(object):
    '''
    A class containing descriptions of PDFrate features. 
    '''
    
    @staticmethod
    def get_feature_count():
        return 135
    
    @staticmethod
    def get_feature_name(i):
        '''
        Returns the i-th feature name. 
        '''
        return copy.copy(_pdfrate_feature_names[i])
    
    @staticmethod
    def get_feature_names():
        '''
        Returns a sorted list of feature names. 
        '''
        return copy.copy(_pdfrate_feature_names)
    
    @staticmethod
    def get_feature_description(feat):
        '''
        Returns the description of the given feature as defined by the 
        FeatureDescriptor.get_feature_descriptions() method. 
        
        feat - name or index of the feature
        '''
        feat_name = FeatureDescriptor.get_feature_names()[feat] if type(feat) == int else feat
        return copy.copy(_pdfrate_feature_descriptions[feat_name])
    
    @staticmethod
    def get_feature_descriptions():
        '''
        For every feature, a dictionary is returned describing that feature:
        its type ('type'), whether it may be altered or not ('edit', with the 
        values 'y' if altering is implemented, 'n' if it's impossible to 
        alter and 'm' if altering is not directly implemented, but the 
        feature value might change by modifying some other features) and 
        the range ('range') within which it may be altered as a tuple of 
        lower and upper bound (FileDefined means that this lower or upper 
        bound cannot be modified further than what is currently in the file). 
        The range represents actual minimum and maximum values seen in the 
        Contagio dataset. 
        '''
        return copy.copy(_pdfrate_feature_descriptions)

    @staticmethod
    def get_feature_mask_numpy():
        '''
        Returns a numpy array with 1 for every feature which is modifiable, 
        otherwise 0. 
        '''
        return numpy.array([1 if _pdfrate_feature_descriptions[name]['edit'] == 'y' else 0 for name in _pdfrate_feature_names])

def features_inverse_standardize(feats, standardizer):
    '''
    Given a standardized feature vector and the standardizer object used 
    to standardize it, performs the inverse transformation and makes sure 
    the resulting data types of all features correspond to their descriptions. 
    '''
    new_feats = list(standardizer.inverse_transform(feats, copy=True))
    for i in range(0, FeatureDescriptor.get_feature_count()):
        t = FeatureDescriptor.get_feature_description(i)['type']
        if t == int:
            new_feats[i] = int(round(new_feats[i]))
        elif t == bool:
            new_feats[i] = False if abs(new_feats[i]) < 0.01 else True
        elif t == float:
            new_feats[i] = float(new_feats[i])
    
    return new_feats

class FeatureEdit(object):
    '''
    A class mimicking PDFrate-like feature reading and additionally enabling 
    the modification of features. 
    
    All methods beginning with 'get_' or 'set_' are considered special, i.e., 
    a method should begin like that if and only if it handles PDFrate-defined 
    features. 
    '''

    def __init__(self, pdf):
        '''
        Constructor. Takes a path to a PDF file as input.
        '''
        self.pdf = pdf
        self.feature_dict = dict()
        self.insert_offset = self._get_startxref_position()
    
    @CachedMethod
    def retrieve_feature_vector(self):
        '''
        Returns a list of feature values, sorted alphabetically by feature 
        name. 
        '''
        features = sorted(self.retrieve_feature_dictionary().items(), key=operator.itemgetter(0))
        return [value for (_, value) in features]
    
    def retrieve_feature_vector_numpy(self):
        '''
        Returns a numpy array of feature values, sorted alphabetically by 
        feature name. 
        '''
        return numpy.array(self.retrieve_feature_vector()).reshape(1, FeatureDescriptor.get_feature_count())
    
    @CachedMethod
    def retrieve_feature_dictionary(self):
        '''
        Returns a dictionary mapping feature names to corresponding feature 
        values for this file. 
        
        This method used to be multithreaded for greater speed, but due to 
        Python bug http://bugs.python.org/issue13817 it no longer is.
        '''
        if len(self.feature_dict) > 0:
            return copy.deepcopy(self.feature_dict)
#         queue_in = Queue.Queue()
#         queue_out = Queue.Queue()
#         print_lock = threading.Lock()
#         print_lock2 = threading.Lock()
#         
#         def thread_print(tid, msg):
#             print_lock2.acquire(True)
#             print '\t'*tid + '%s: %s' % (tid, msg)
#             print_lock2.release()
#         
#         def thread_function(tid):
#             while True:
#                 thread_print(tid, 'running')
#                 method = ''
#                 try:
#                     method = queue_in.get_nowait()
#                     thread_print(tid, 'Got "%s"' % method)
#                 except Queue.Empty:
#                     thread_print(tid, 'Queue.Empty')
#                     return
#                 r = 0
#                 try:
#                     # http://bugs.python.org/issue13817
#                     r = getattr(self, 'get_' + method)()
#                     thread_print(tid, 'got_attr')
#                 except NotImplementedError as ex:
#                     r = ex
#                     thread_print(tid, 'got not impl')
#                 except Exception as ex:
#                     r = ex
#                     thread_print(tid, 'got exception')
#                     print_lock.acquire(True)
#                     sys.stderr.write('#'*10)
#                     traceback.print_exc(file=sys.stderr)
#                     sys.stderr.write('#'*10)
#                     print_lock.release()
#                 queue_out.put((method, r))
#                 thread_print(tid, 'put method %s' % method)
#                 queue_in.task_done()
#                 thread_print(tid, 'task done')
#         
#         for method in FeatureDescriptor.get_feature_names():
#             queue_in.put(method)
# 
#         for tid in range(10):
#             thread = threading.Thread(target=thread_function, args=[tid])
#             thread.daemon = True
#             thread.name = tid
#             thread.start()
#         
#         queue_in.join()
#         feature_dict = dict()
#         while not queue_out.empty():
#             r = queue_out.get()
#             feature_dict[r[0]] = r[1]
        feature_dict = dict()
        for method in FeatureDescriptor.get_feature_names():
            try:
                r = getattr(self, 'get_' + method)()
            except NotImplementedError as ex:
                r = ex
            except Exception as ex:
                r = ex
                sys.stderr.write('#'*10)
                traceback.print_exc(file=sys.stderr)
                sys.stderr.write('#'*10)
            feature_dict[method] = r
        self.feature_dict = feature_dict
        return copy.deepcopy(feature_dict)
    
    def retrieve_feature_bounds(self):
        '''
        Returns two lists corresponding to the upper and lower bounds for feature 
        modifications of a given object. This method is *not* static because some
        bounds are object-dependent. The bounds are returned for all features, 
        including the non-modifiable ones.
        '''
        def check_current_value(name,value):
            if value == FileDefined:
                return getattr(self, 'get_'+name)()
            else:
                return value
        
        lb = []
        ub = []
        fd = FeatureDescriptor.get_feature_descriptions()
        for key in sorted(fd.keys()):
            value = fd[key]
            lb.append(check_current_value(key,value['range'][0]))
            ub.append(check_current_value(key,value['range'][1]))
        return (numpy.array(lb),numpy.array(ub))
    
    @CachedMethod
    def get_size(self):
        return os.path.getsize(self.pdf)
    
    @CachedMethod
    def get_version(self):
        r = _perl_regex(r'print $1 while /%PDF-1\.(\d)/g', self.pdf)
        # Orgnal
        # r = r.split('\n')[0
        # New
        r = r.split(b'\n')[0]
        return int(r) if r else 0
    
    @CachedMethod
    def get_count_obj(self):
        r = _perl_regex(r'while (/\d+\s+\d+\s+obj/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_endobj(self):
        r = _perl_regex(r'while (/\s+endobj\s+/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_stream(self):
        r = _perl_regex(r'while (/[^\w]stream\s+/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_endstream(self):
        r = _perl_regex(r'while (/[^\w]endstream\s+/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_xref(self):
        r = _perl_regex(r'while (/[^\w\d]xref[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_trailer(self):
        r = _perl_regex(r'while (/[^\w\d]trailer[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_startxref(self):
        r = _perl_regex(r'while (/[^\w\d]startxref[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_eof(self):
        r = _perl_regex(r'while (/%EOF/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_page(self):
        r = _perl_regex(r'while (/\/Page[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_objstm(self):
        r = _perl_regex(r'while (/\/ObjStm[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_js(self):
        # PDFrate doesn't always find this!
        r = _perl_regex(r'while (/\/JS[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_javascript(self):
        r = _perl_regex(r'while (/\/JavaScript[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_action(self):
        r = _perl_regex(r'while (/\/(OpenAction|AA)[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_acroform(self):
        # Not present in the PDFrate output!
        r = _perl_regex(r'while (/(\/AcroForm)[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_font(self):
        r = _perl_regex(r'while (/(\/Font)[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_stream_diff(self):
        return self.get_count_stream() - self.get_count_endstream()
    
    @CachedMethod
    def __get_moddate_raw(self):

        # Debug
        # print(_perl_regex(r'print $1 while /\/ModDate \((.*?)\)/g', self.pdf))

        # Original
        # return _perl_regex(r'print $1 while /\/ModDate\((.*?)\)/g', self.pdf).splitlines()
        # New
        return _perl_regex(r'print $1 while /\/ModDate\((.*?)\)/g', self.pdf).splitlines()

    @CachedMethod
    def get_moddate_ts(self):
        r = self.__get_moddate_raw()

        # Debug
        # print('moddate raw', r)
        # print(r[-1])

        # Orginal
        # if r: r = r[-1]
        # New
        if r: r = r[-1].decode(errors='replace')

        # Date format: D:YYYYMMDDHHmmSSOHH'mm
        if len(r) < 6 or r[:2] != 'D:': return -1
        timestamp = 0
        try:
            YYYY = int(r[2:6])
            MM = int(r[6:8]) if len(r) > 6 else 1
            DD = int(r[8:10]) if len(r) > 8 else 1
            HH1 = int(r[10:12]) if len(r) > 10 else 0
            mm1 = int(r[12:14]) if len(r) > 12 else 0
            SS = int(r[14:16]) if len(r) > 14 else 0
            O = r[16] if len(r) > 16 else 'Z'

            # Debug
            # print('here', YYYY, MM, DD, HH1, mm1, SS, O)

            # Original
            HH2 = int(r[17:19]) if len(r) > 17 else 0
            # New
            # HH2 = int(r[17:18]) if len(r) > 17 else 0

            # r[19] == "'"
            mm2 = int(r[20:22]) if len(r) > 20 else 0
            tz_sign = '+' if O in ['+', 'Z'] else '-'
            datetime_str = '{Y:0>4}{m:0>2}{d:0>2}{H:0>2}{M:0>2}{S:0>2}\
+0000'.format(Y=YYYY, m=MM, d=DD, H=HH1, M=mm1, S=SS, sign=tz_sign, zH=HH2, zM=mm2)

            # Debug
            # print('datetime string', datetime_str)

            timestamp = dateutil.parser.parse(datetime_str)
            return int(calendar.timegm(timestamp.utctimetuple()))
        except:
            return -1
    
    @CachedMethod
    def get_moddate_tz(self):
        r = self.__get_moddate_raw()

        # Orginal
        # if r: r = r[-1]
        # New
        if r: r = r[-1].decode(errors='replace')

        # Debug
        # print('moddate raw', r)

        # Date format: D:YYYYMMDDHHmmSSOHH'mm
        if len(r) < 6 or r[:2] != 'D:': # minimum is D:YYYY
            return -1

        moddate_tz = 0
        try: 
            O = r[16] if len(r) > 16 else 'Z'

            # Original
            HH2 = int(r[17:19]) if len(r) > 17 else 0
            # New
            # HH2 = int(r[17:18]) if len(r) > 17 else 0

            mm2 = int(r[20:22]) if len(r) > 20 else 0
            tz_sign = '+' if O in ['+', 'Z'] else '-'
            moddate_tz = HH2 * 3600 + mm2 * 60
            if tz_sign == '-': moddate_tz = -moddate_tz
        except Exception:
            return -1
        return moddate_tz
    
    @CachedMethod
    def __get_createdate_raw(self):
        return _perl_regex(r'print $1 while /<x[am]p:CreateDate>(.*?)<\/x[am]p:CreateDate>/g', self.pdf).splitlines()
    
    @CachedMethod
    def get_createdate_ts(self):
        r = self.__get_createdate_raw()
        if not r: 
            return -1
        else: 
            r = r[-1]
        try:
            timestamp = dateutil.parser.parse(r)
            return int(calendar.timegm(timestamp.utctimetuple()))
        except:
            return -1
    
    @CachedMethod
    def get_createdate_tz(self):
        r = self.__get_createdate_raw()
        if not r: 
            return -1
        else: 
            r = r[-1]
        try:
            timezone = dateutil.parser.parse(r).strftime("%z")
            if not timezone:
                return -1
            tz_sec = int(timezone[1:3]) * 3600 + int(timezone[3:5]) * 60
            return tz_sec if timezone[0] == '+' else -tz_sec
        except Exception:
            return -1
    
    @CachedMethod
    def get_createdate_version_ratio(self):
        ts = self.get_createdate_ts()
        if ts == -1: return -1
        v = self.get_version()
        # Original
        # return self.get_createdate_ts() / 86400.0 / v if v != 0 else 0
        # New
        return int(self.get_createdate_ts() / 86400.0 / v) if v != 0 else 0

    @CachedMethod
    def get_moddate_version_ratio(self):
        ts = self.get_moddate_ts()
        if ts == -1: return -1
        v = self.get_version()
        # Original
        # return self.get_moddate_ts() / 86400.0 / v if v != 0 else 0
        # New
        return int(self.get_moddate_ts() / 86400.0 / v) if v != 0 else 0


    @CachedMethod
    def get_createdate_dot(self):
        return self.__get_createdate_raw().count('.')
    
    @CachedMethod
    def get_moddate_dot(self):
        return self.__get_moddate_raw().count('.')
    
    @CachedMethod
    def __get_pdfid0_raw(self):
        return _perl_regex(r'print $1 while /\/ID\[[^\d|A-F|a-f]*([\d|A-F|a-f]*)/g', self.pdf).splitlines()
    
    @CachedMethod
    def __get_pdfid0(self):
        return self.__get_pdfid0_raw()[-1].decode(errors='replace') if self.__get_pdfid0_raw() else ''
    
    @CachedMethod
    def get_pdfid0_len(self):
        return len(self.__get_pdfid0())
    
    @CachedMethod
    def get_pdfid0_lc(self):
        # Orginal
        # return len(filter(str.islower, self.__get_pdfid0()))
        # New
        return sum(1 for i in filter(str.islower, self.__get_pdfid0()))

    @CachedMethod
    def get_pdfid0_uc(self):
        # Orginal
        # return len(filter(str.isupper, self.__get_pdfid0()))
        # New
        return sum(1 for _ in filter(str.isupper, self.__get_pdfid0()))
    
    @CachedMethod
    def get_pdfid0_num(self):
        # Original
        # return len(filter(str.isdigit, self.__get_pdfid0()))
        # New
        return sum(1 for _ in filter(str.isdigit, self.__get_pdfid0()))
    
    @CachedMethod
    def get_pdfid0_oth(self):
        # Original
        # return self.get_pdfid0_len() - self.get_pdfid0_lc() - self.get_pdfid0_uc() - self.get_pdfid0_num()
        # New
        return self.get_pdfid0_len() - self.get_pdfid0_lc() - self.get_pdfid0_uc() - self.get_pdfid0_num() - self.get_pdfid0_dot()

    @CachedMethod
    def get_pdfid0_dot(self):

        # Debug
        # print('self.__get_pdfid0()', self.__get_pdfid0())

        return self.__get_pdfid0().count('.')

    @CachedMethod
    def __get_pdfid1_raw(self):
        return _perl_regex(r'print $1 while /\/ID\[[^\d|A-F|a-f]*[\d|A-F|a-f]*[^\d|A-F|a-f]*([\d|A-F|a-f]*)/g', self.pdf).splitlines()
    
    @CachedMethod
    def __get_pdfid1(self):
        return self.__get_pdfid1_raw()[-1].decode(errors='replace') if self.__get_pdfid1_raw() else ''
    
    @CachedMethod
    def get_pdfid1_len(self):
        return len(self.__get_pdfid1())
    
    @CachedMethod
    def get_pdfid1_lc(self):
        # Original
        # return len(filter(str.islower, self.__get_pdfid1()))
        # New
        return sum(1 for _ in filter(str.islower, self.__get_pdfid1()))
    
    @CachedMethod
    def get_pdfid1_uc(self):
        # Original
        # return len(filter(str.isupper, self.__get_pdfid1()))
        # New
        return sum(1 for _ in filter(str.isupper, self.__get_pdfid1()))
    
    @CachedMethod
    def get_pdfid1_num(self):
        # Original
        # return len(filter(str.isdigit, self.__get_pdfid1()))
        # New
        return sum(1 for _ in filter(str.isdigit, self.__get_pdfid1()))
    
    @CachedMethod
    def get_pdfid1_oth(self):
        # Original
        # return self.get_pdfid1_len() - self.get_pdfid1_lc() - self.get_pdfid1_uc() - self.get_pdfid1_num()
        # New
        return self.get_pdfid1_len() - self.get_pdfid1_lc() - self.get_pdfid1_uc() - self.get_pdfid1_num() - self.get_pdfid1_dot()

    @CachedMethod
    def get_pdfid1_dot(self):
        return self.__get_pdfid1().count('.')

    @CachedMethod
    def get_pdfid_mismatch(self):
        return self.__get_pdfid0() != self.__get_pdfid1()
    
    @CachedMethod
    def __get_title_raw(self):
        return _perl_regex(r'print $1 while /\/Title[^\w\d]*\((.*?[^\\]?)\)/g', self.pdf).splitlines()

    @CachedMethod
    def __get_title(self):
        return _sanitize_PDF_literal_string(self.__get_title_raw()[-1]).decode(errors='replace') if self.__get_title_raw() else ''
    
    @CachedMethod
    def get_title_len(self):
        return len(self.__get_title())
    
    @CachedMethod
    def get_title_lc(self):
        # Original
        # return len(filter(str.islower, self.__get_title()))
        # New
        return sum(1 for _ in filter(str.islower, self.__get_title()))

    @CachedMethod
    def get_title_uc(self):
        # Original
        # return len(filter(str.isupper, self.__get_title()))
        # New
        return sum(1 for _ in filter(str.isupper, self.__get_title()))

    @CachedMethod
    def get_title_num(self):
        # Original
        # return len(filter(str.isdigit, self.__get_title()))
        # New
        return sum(1 for _ in filter(str.isdigit, self.__get_title()))

    @CachedMethod
    def get_title_dot(self):
        return self.__get_title().count('.')

    @CachedMethod
    def get_title_oth(self):
        # Original
        # return self.get_title_len() - self.get_title_lc() - self.get_title_uc() - self.get_title_num()
        # New
        return self.get_title_len() - self.get_title_lc() - self.get_title_uc() - self.get_title_num() - self.get_title_dot()

    @CachedMethod
    def __get_author_raw(self):
        return _perl_regex(r'print $1 while /\/Author[^\w\d]*\((.*?[^\\]?)\)/g', self.pdf).splitlines()
    
    @CachedMethod
    def __get_author(self):
        return _sanitize_PDF_literal_string(self.__get_author_raw()[-1]).decode(errors='replace') if self.__get_author_raw() else ''

    @CachedMethod
    def get_author_len(self):
        return len(self.__get_author())
    
    @CachedMethod
    def get_author_lc(self):
        # Original
        # return len(filter(str.islower, self.__get_author()))
        # New
        return sum(1 for i in filter(str.islower, self.__get_author()))
    
    @CachedMethod
    def get_author_uc(self):
        # Original
        # return len(filter(str.isupper, self.__get_author()))
        # New
        return sum(1 for _ in filter(str.isupper, self.__get_author()))
    
    @CachedMethod
    def get_author_num(self):
        # Original
        # return len(filter(str.isdigit, self.__get_author()))
        # New
        return sum(1 for _ in filter(str.isdigit, self.__get_author()))
    
    @CachedMethod
    def get_author_oth(self):
        # Original
        # return self.get_author_len() - self.get_author_lc() - self.get_author_uc() - self.get_author_num()
        # New
        return self.get_author_len() - self.get_author_lc() - self.get_author_uc() - self.get_author_num() - self.get_author_dot()

    @CachedMethod
    def get_author_dot(self):

        # Debug
        # print(self.__get_author().decode(errors='replace'))

        return self.__get_author().count('.')

    @CachedMethod
    def __get_producer_raw(self):
        r1 = _perl_regex(r'print $1 while /\/Producer[^\w\d]*\((.*?[^\\]?)\)/g', self.pdf)
        r2 = _perl_regex(r'print $1 while /Producer>(.*?)<\//g', self.pdf)
        return (r1 + r2).splitlines()
    
    @CachedMethod
    def __get_producer(self):
        return _sanitize_PDF_literal_string(self.__get_producer_raw()[-1]).decode(errors='replace') if self.__get_producer_raw() else ''
    
    @CachedMethod
    def get_producer_len(self):
        return len(self.__get_producer())
    
    @CachedMethod
    def get_producer_lc(self):
        # Original
        # return len(filter(str.islower, self.__get_producer()))
        # New
        return sum(1 for _ in filter(str.islower, self.__get_producer()))
    
    @CachedMethod
    def get_producer_uc(self):
        # Original
        # return len(filter(str.isupper, self.__get_producer()))
        # New
        return sum(1 for _ in filter(str.isupper, self.__get_producer()))
    
    @CachedMethod
    def get_producer_num(self):
        # Original
        # return len(filter(str.isdigit, self.__get_producer()))
        # New
        return sum(1 for _ in filter(str.isdigit, self.__get_producer()))
    
    @CachedMethod
    def get_producer_oth(self):
        # Original
        # return self.get_producer_len() - self.get_producer_lc() - self.get_producer_uc() - self.get_producer_num()
        # New
        return self.get_producer_len() - self.get_producer_lc() - self.get_producer_uc() - self.get_producer_num() - self.get_producer_dot()

    @CachedMethod
    def get_producer_dot(self):
        return self.__get_producer().count('.')

    @CachedMethod
    def __get_creator_raw(self):
        r1 = _perl_regex(r'print $1 while /\/Creator[^\w\d]*\((.*?[^\\]?)\)/g', self.pdf)
        r2 = _perl_regex(r'print $1 while /CreatorTool>(.*?)<\//g', self.pdf)
        return (r1 + r2).splitlines()
    
    @CachedMethod
    def __get_creator(self):
        return _sanitize_PDF_literal_string(self.__get_creator_raw()[-1]).decode(errors='replace') if self.__get_creator_raw() else ''
    
    @CachedMethod
    def get_creator_len(self):
        return len(self.__get_creator())
    
    @CachedMethod
    def get_creator_lc(self):
        # Original
        # return len(filter(str.islower, self.__get_creator()))
        # New
        return sum(1 for _ in filter(str.islower, self.__get_creator()))
    
    @CachedMethod
    def get_creator_uc(self):
        # Original
        # return len(filter(str.isupper, self.__get_creator()))
        # New
        return sum(1 for _ in filter(str.isupper, self.__get_creator()))
    
    @CachedMethod
    def get_creator_num(self):
        # Original
        # return len(filter(str.isdigit, self.__get_creator()))
        # New
        return sum(1 for _ in filter(str.isdigit, self.__get_creator()))
    
    @CachedMethod
    def get_creator_oth(self):
        # Original
        # return self.get_creator_len() - self.get_creator_lc() - self.get_creator_uc() - self.get_creator_num()
        # New
        return self.get_creator_len() - self.get_creator_lc() - self.get_creator_uc() - self.get_creator_num() - self.get_creator_dot()

    @CachedMethod
    def get_creator_dot(self):
        return self.__get_creator().count('.')

    @CachedMethod
    def __get_subject_raw(self):
        return _perl_regex(r'print $1 while /\/Subject[^\w\d]*\((.*?[^\\]?)\)/g', self.pdf).splitlines()
    
    @CachedMethod
    def __get_subject(self):
        # Original
        # return _sanitize_PDF_literal_string(self.__get_subject_raw()[-1]) if self.__get_subject_raw() else ''
        # New
        return _sanitize_PDF_literal_string(self.__get_subject_raw()[-1]).decode(errors='replace') if self.__get_subject_raw() else ''

    @CachedMethod
    def get_subject_len(self):
        return len(self.__get_subject())
    
    @CachedMethod
    def get_subject_lc(self):
        # Original
        # return len(filter(str.islower, self.__get_subject()))
        # New
        return sum(1 for _ in filter(str.islower, self.__get_subject()))
    
    @CachedMethod
    def get_subject_uc(self):
        # Original
        # return len(filter(str.isupper, self.__get_subject()))
        # New
        return sum(1 for _ in filter(str.isupper, self.__get_subject()))
    
    @CachedMethod
    def get_subject_num(self):
        # Original
        # return len(filter(str.isdigit, self.__get_subject()))
        # New
        return sum(1 for _ in filter(str.isdigit, self.__get_subject()))
    
    @CachedMethod
    def get_subject_oth(self):
        # Original
        # return self.get_subject_len() - self.get_subject_lc() - self.get_subject_uc() - self.get_subject_num()
        # New
        return self.get_subject_len() - self.get_subject_lc() - self.get_subject_uc() - self.get_subject_num() - self.get_subject_dot()

    @CachedMethod
    def get_subject_dot(self):
        return self.__get_subject().count('.')

    @CachedMethod
    def __get_keywords_raw(self):
        r1 = _perl_regex(r'print $1 while /\/Keywords[^\w\d]*\((.*?[^\\]?)\)/g', self.pdf)
        r2 = _perl_regex(r'print $1 while /\<pdf:Keywords>(.*?)<\/pdf:Keywords>/g', self.pdf)
        return (r1 + r2).splitlines()
    
    @CachedMethod
    def __get_keywords(self):
        # Old
        # return _sanitize_PDF_literal_string(self.__get_keywords_raw()[-1]) if self.__get_keywords_raw() else ''
        # New
        return _sanitize_PDF_literal_string(self.__get_keywords_raw()[-1]).decode(errors='replace') if self.__get_keywords_raw() else ''

    @CachedMethod
    def get_keywords_len(self):
        return len(self.__get_keywords())
    
    @CachedMethod
    def get_keywords_lc(self):
        # Original
        # return len(filter(str.islower, self.__get_keywords()))
        # New
        return sum(1 for _ in filter(str.islower, self.__get_keywords()))
    
    @CachedMethod
    def get_keywords_uc(self):
        # Original
        # return len(filter(str.isupper, self.__get_keywords()))
        # New
        return sum(1 for _ in filter(str.isupper, self.__get_keywords()))
    
    @CachedMethod
    def get_keywords_num(self):
        # Original
        # return len(filter(str.isdigit, self.__get_keywords()))
        # New
        return sum(1 for _ in filter(str.isdigit, self.__get_keywords()))
    
    @CachedMethod
    def get_keywords_oth(self):
        # Original
        # return self.get_keywords_len() - self.get_keywords_lc() - self.get_keywords_uc() - self.get_keywords_num()
        # New
        return self.get_keywords_len() - self.get_keywords_lc() - self.get_keywords_uc() - self.get_keywords_num() - self.get_keywords_dot()

    @CachedMethod
    def get_keywords_dot(self):
        return self.__get_keywords().count('.')

    @CachedMethod
    def get_count_page_obs(self):
        r = _perl_regex(r'while (/\/(P|#50)(a|#61)(g|#67)(e|#65)[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) - self.get_count_page() if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_objstm_obs(self):
        r = _perl_regex(r'while (/\/(O|#4[fF])(b|#62)(j|#6[aA])(S|#53)(t|#74)(m|#6[Dd])[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) - self.get_count_objstm() if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_js_obs(self):
        r = _perl_regex(r'while (/\/(J|#4[aA])(S|#53)[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) - self.get_count_js() if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_javascript_obs(self):
        r = _perl_regex(r'while (/\/(J|#4[aA])(a|#61)(v|#76)(a|#61)(S|#53)(c|#63)(r|#72)(i|#69)(p|#70)(t|#74)[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) - self.get_count_javascript() if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_action_obs(self):
        r = _perl_regex(r'while (/\/((O|#4F)(p|#70)(e|#65)(n|#6[eE])(A|#41)(c|#63)(t|#74)(i|#69)(o|#6[fF])(n|#6[eE])|(A|#41)(A|#41))[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) - self.get_count_action() if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_acroform_obs(self):
        r = _perl_regex(r'while (/\/(A|#41)(c|#63)(r|#72)(o|#6[fF])(F|#46)(o|#6[fF])(r|#72)(m|#6[dD])[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) - self.get_count_acroform() if len(r) > 1 else 0
    
    @CachedMethod
    def get_count_font_obs(self):
        r = _perl_regex(r'while (/\/(F|#46)(o|#6[fF])(n|#6[eE])(t|#74)[^\w\d]/g) {$c++} print $c', self.pdf)
        return int(r) - self.get_count_font() if len(r) > 1 else 0
    
    @CachedMethod
    def get_delta_ts(self):
        return self.get_createdate_ts() - self.get_moddate_ts()
    
    @CachedMethod
    def get_delta_tz(self):
        return self.get_createdate_tz() - self.get_moddate_tz()
    
    @CachedMethod
    def get_moddate_mismatch(self):
        return len(set(self.__get_moddate_raw()))
    
    @CachedMethod
    def get_createdate_mismatch(self):
        return len(set(self.__get_createdate_raw()))
    
    @CachedMethod
    def get_pdfid0_mismatch(self):
        return len(set(self.__get_pdfid0_raw()))
    
    @CachedMethod
    def get_pdfid1_mismatch(self):
        return len(set(self.__get_pdfid1_raw()))
    
    @CachedMethod
    def get_title_mismatch(self):
        return len(set(self.__get_title_raw()))
    
    @CachedMethod
    def get_author_mismatch(self):
        return len(set(self.__get_author_raw()))
    
    @CachedMethod
    def get_producer_mismatch(self):
        return len(set(self.__get_producer_raw()))
    
    @CachedMethod
    def get_creator_mismatch(self):
        return len(set(self.__get_creator_raw()))
    
    @CachedMethod
    def get_company_mismatch(self):
        companies = _perl_regex(r'print $1 while /\/Company[^\w\d]*\((.*?[^\\]?)\)/g', self.pdf)
        return len(set(companies.splitlines()))
    
    @CachedMethod
    def get_subject_mismatch(self):
        return len(set(self.__get_subject_raw()))
    
    @CachedMethod
    def get_keywords_mismatch(self):
        return len(set(self.__get_keywords_raw()))
    
    @CachedMethod
    def __get_boxes_raw(self):
        r = _perl_regex(r'print sprintf("%d ", ($rr = $1) =~ tr/\r\n/  /), $rr while /\[\s*((([+|-]?(\d+\.?\d*|\d*\.?\d+))\s+){3}([+|-]?(\d+\.?\d*|\d*\.?\d+)))\s*\]/g', self.pdf)
        boxes = []
        for box in r.splitlines():
            # Original
            # dims, _ = _regex_pdf_box.subn(r'\1 \2 \3 \4', box)
            # New
            dims, _ = _regex_pdf_box.subn(r'\1 \2 \3 \4', box.decode(errors='replace'))
            dims = [float(dim) for dim in dims.split(' ')]
            boxes.append(dims)
        return boxes
    
    @staticmethod
    def __is_box_a4(box):
        return box[0] == 0 and box[1] == 0 and box[2] >= 596 and box[2] <= 599  and box[3] >= 841 and box[3] <= 844
    
    @staticmethod
    def __is_box_letter(box):
        return box[0] == 0 and box[1] == 0 and box[2] >= 610 and box[2] <= 613  and box[3] >= 790 and box[3] <= 793
    
    @staticmethod
    def __is_box_overlap(box):
        return box[0] == 0 and box[1] == 0 and box[2] >= 596 and box[2] <= 599  and box[3] >= 790 and box[3] <= 793
    
    @staticmethod
    def __is_box_legal(box):
        return box[0] == 0 and box[1] == 0 and box[2] >= 610 and box[2] <= 613  and box[3] >= 1006 and box[3] <= 1009
    
    @staticmethod
    def __is_box_other(box):
        return not (FeatureEdit.__is_box_a4(box) or FeatureEdit.__is_box_letter(box) or FeatureEdit.__is_box_overlap(box) or FeatureEdit.__is_box_legal(box))
    
    @CachedMethod
    def get_count_box_a4(self):
        count = 0
        for box in self.__get_boxes_raw():
            if self.__is_box_a4(box):
                count += 1
        return count
    
    @CachedMethod
    def get_count_box_letter(self):
        count = 0
        for box in self.__get_boxes_raw():
            if self.__is_box_letter(box):
                count += 1
        return count
    
    @CachedMethod
    def get_count_box_overlap(self):
        count = 0
        for box in self.__get_boxes_raw():
            if self.__is_box_overlap(box):
                count += 1
        return count
    
    @CachedMethod
    def get_count_box_legal(self):
        count = 0
        for box in self.__get_boxes_raw():
            if self.__is_box_legal(box):
                count += 1
        return count
    
    @CachedMethod
    def get_count_box_other(self):
        count = 0
        for box in self.__get_boxes_raw():
            if self.__is_box_other(box):
                count += 1
        return count
    
    @CachedMethod
    def get_box_other_only(self):
        for box in self.__get_boxes_raw():
            if not self.__is_box_other(box):
                return False
        return True
    
    @CachedMethod
    def get_box_nonother_types(self):
        count = 0
        for box in self.__get_boxes_raw():
            if not self.__is_box_other(box):
                count += 1
        return count
    
    @CachedMethod
    def __get_images_raw(self):
        r = _perl_regex(r'print sprintf("%d ", ($rr = $1) =~ tr/\r\n/  /), $rr while /(<<[^<]*?\/Height\s+\d+.*?>>)/g', self.pdf)
        image_sizes = []

        # New
        r = r.decode(errors='replace')

        for line in r.split('\n'):
            if not line:
                continue
            height, _ = _regex_pdf_image_height.subn(r'\1', line)
            width, nsubs = _regex_pdf_image_width.subn(r'\1', line)
            if nsubs != 1:
                # Not an image
                continue
            image_sizes.append(int(height) * int(width))
        return image_sizes
    
    @CachedMethod
    def get_image_totalpx(self):
        return sum(self.__get_images_raw())
    
    @CachedMethod
    def get_count_image_total(self):
        return len(self.__get_images_raw())
    
    @CachedMethod
    def get_count_image_xsmall(self):
        return len([1 for image_size in self.__get_images_raw() if image_size <= 4096])
    
    @CachedMethod
    def get_count_image_small(self):
        return len([1 for image_size in self.__get_images_raw() if image_size > 4096 and image_size <= 64000])
    
    @CachedMethod
    def get_count_image_med(self):
        return len([1 for image_size in self.__get_images_raw() if image_size > 64000 and image_size <= 786432])
    
    @CachedMethod
    def get_count_image_large(self):
        return len([1 for image_size in self.__get_images_raw() if image_size > 786432 and image_size <= 12582912])
    
    @CachedMethod
    def get_count_image_xlarge(self):
        return len([1 for image_size in self.__get_images_raw() if image_size > 12582912])
    
    @CachedMethod
    def get_image_mismatch(self):
        return max(0, len(set(self.__get_images_raw())) - 1)
    
    @CachedMethod
    def get_ratio_imagepx_size(self):
        return self.get_image_totalpx() / float(self.get_size())
    
    @CachedMethod
    def get_ratio_size_obj(self):
        return self.get_size() / (self.get_count_obj() + 1e-6)
    
    @CachedMethod
    def get_ratio_size_stream(self):
        return self.get_size() / (self.get_count_stream() + 1e-6)
    
    @CachedMethod
    def get_ratio_size_page(self):
        return self.get_size() / (self.get_count_page() + 1e-6)
    
    @CachedMethod
    def __get_obj_sizes_raw(self):
        r1 = _perl_regex(r'print sprintf("%d", @-[1]) while /\d+\s+\d+\s+(obj)/g', self.pdf)
        r2 = _perl_regex(r'print sprintf("%d", @-[1]) while /(endobj)/g', self.pdf)
        if r1:
            # Original
            # r1 = [int(r) for r in r1.split('\n') if r]
            # New
            r1 = [int(r) for r in r1.split(b'\n') if r]
        else:
            return [0]
        if r2:
            # Original
            # r2 = [int(r) for r in r2.split('\n') if r]
            # New
            r2 = [int(r) for r in r2.split(b'\n') if r]
        else:
            return [0]
        return [b - a for a, b in zip(r1, r2) if (b - a) > 0]
#         r = re.compile(r'\d+\s+\d+\s+(obj)')
#         text = ''
#         with open(self.pdf, 'rb') as fin:
#             text = fin.read()
#         res = []
#         for inst in r.finditer(text):
#             starti = text.find('obj', inst.start())
#             endi = text.find('endobj', starti)
#             if endi == -1:
#                 break
#             res.append(endi - starti)
#         return res if res else [0]
    
    @CachedMethod
    def get_len_obj_min(self):
        return min(self.__get_obj_sizes_raw())
    
    @CachedMethod
    def get_len_obj_max(self):
        return max(self.__get_obj_sizes_raw())
    
    @CachedMethod
    def get_len_obj_avg(self):
        sizes = self.__get_obj_sizes_raw()
        return sum(sizes) / float(len(sizes))
    
    @CachedMethod
    def __get_stream_sizes_raw(self):
        r = _perl_regex(r'print sprintf("%d", @-[2]-@-[1]) while /[^\w](s)tream\s.*?[^\w](e)ndstream\s/sg', self.pdf)
        if not r: return [0]
        # Original
        # return [int(line) for line in r.split('\n') if line]
        # New
        return [int(line) for line in r.split(b'\n') if line]
    
    @CachedMethod
    def get_len_stream_min(self):
        return min(self.__get_stream_sizes_raw())
    
    @CachedMethod
    def get_len_stream_max(self):
        return max(self.__get_stream_sizes_raw())
    
    @CachedMethod
    def get_len_stream_avg(self):
        sizes = self.__get_stream_sizes_raw()
        return sum(sizes) / float(len(sizes)) if len(sizes) > 0 else 0.0
    
    @CachedMethod
    def __get_eof_positions_raw(self):
        r = _perl_regex(r'print sprintf("%d", @-[1]) while /%(E)OF/g', self.pdf)
        if not r: return [0]
        # Original
        # return [int(line) for line in r.split('\n') if line]
        # New
        return [int(line) for line in r.split(b'\n') if line]
    
    @CachedMethod
    def get_pos_eof_min(self):
        return min(self.__get_eof_positions_raw()) / float(self.get_size())
    
    @CachedMethod
    def get_pos_eof_max(self):
        return max(self.__get_eof_positions_raw()) / float(self.get_size())
    
    @CachedMethod
    def get_pos_eof_avg(self):
        sizes = self.__get_eof_positions_raw()
        return sum(sizes) / float(len(sizes) * self.get_size())
    
    @CachedMethod
    def __get_page_positions_raw(self):
        r = _perl_regex(r'print sprintf("%d", @-[1]) while /\/(P)age[^\w\d]/g', self.pdf)
        # Original
        # return [int(line) for line in r.split('\n') if line]
        # New
        return [int(line) for line in r.split(b'\n') if line]
    
    @CachedMethod
    def get_pos_page_min(self):
        pos = self.__get_page_positions_raw()
        return min(pos) / float(self.get_size()) if pos else -1.0
    
    @CachedMethod
    def get_pos_page_max(self):
        pos = self.__get_page_positions_raw()
        return max(pos) / float(self.get_size()) if pos else -1.0
    
    @CachedMethod
    def get_pos_page_avg(self):
        pos = self.__get_page_positions_raw()
        return sum(pos) / float(len(pos) * self.get_size()) if pos else -1.0
    
    @CachedMethod
    def __get_acroform_positions_raw(self):
        r = _perl_regex(r'print sprintf("%d", @-[1]) while /(\/AcroForm)[^\w\d]/g', self.pdf)
        # Original
        # return [int(line) for line in r.split('\n') if line]
        # New
        return [int(line) for line in r.split(b'\n') if line]
    
    @CachedMethod
    def get_pos_acroform_min(self):
        pos = self.__get_acroform_positions_raw()
        return min(pos) / float(self.get_size()) if pos else -1.0
    
    @CachedMethod
    def get_pos_acroform_max(self):
        pos = self.__get_acroform_positions_raw()
        return max(pos) / float(self.get_size()) if pos else -1.0
    
    @CachedMethod
    def get_pos_acroform_avg(self):
        pos = self.__get_acroform_positions_raw()
        return sum(pos) / float(len(pos) * self.get_size()) if pos else -1.0
    
    @CachedMethod
    def __get_box_positions_raw(self):
        r = _perl_regex(r'print sprintf("%d", @-[1]) while /\[\s*((([+|-]?(\d+\.?\d*|\d*\.?\d+))\s+){3}([+|-]?(\d+\.?\d*|\d*\.?\d+)))\s*\]/g', self.pdf)
        # Original
        # return [int(line) for line in r.split('\n') if line]
        # New
        return [int(line) for line in r.split(b'\n') if line]
    
    @CachedMethod
    def get_pos_box_min(self):
        pos = self.__get_box_positions_raw()
        return min(pos) / float(self.get_size()) if pos else -1.0
    
    @CachedMethod
    def get_pos_box_max(self):
        pos = self.__get_box_positions_raw()
        return max(pos) / float(self.get_size()) if pos else -1.0
    
    @CachedMethod
    def get_pos_box_avg(self):
        pos = self.__get_box_positions_raw()
        return sum(pos) / float(len(pos) * self.get_size()) if pos else -1.0
    
    @CachedMethod
    def __get_image_positions_raw(self):
        r = _perl_regex(r'print sprintf("%d", @-[1]) while /(<<(?=.*\/Height\s+\d+)(?=.*\/Width\s+\d+)(?:.*?<<.*>>)*.*?>>)/g', self.pdf)
        # Original
        # return [int(line) for line in r.split('\n') if line]
        # New
        return [int(line) for line in r.split(b'\n') if line]
    
    @CachedMethod
    def get_pos_image_min(self):
        pos = self.__get_image_positions_raw()
        return min(pos) / float(self.get_size()) if pos else -1.0
    
    @CachedMethod
    def get_pos_image_max(self):
        pos = self.__get_image_positions_raw()
        return max(pos) / float(self.get_size()) if pos else -1.0
    
    @CachedMethod
    def get_pos_image_avg(self):
        pos = self.__get_image_positions_raw()
        return sum(pos) / float(len(pos) * self.get_size()) if pos else -1.0
    
    @CachedMethod
    def _get_startxref_position(self):
        r = _perl_regex(r'print sprintf("%d", @-[1]) while /[^\w\d](startxref)[^\w\d]/g', self.pdf)
        # Original
        # r = r.split('\n')
        # New
        r = r.split(b'\n')
        return int(r[-2]) if len(r) > 1 else self.get_size()
    
    def check_feature_change_valid(self, feat, feat_val):
        feat_name = FeatureDescriptor.get_feature_name(feat) if type(feat) == int else feat
        feat_desc = FeatureDescriptor.get_feature_descriptions()[feat_name]
        if feat_desc['type'] != type(feat_val):
            return TypeError("Got {got}, expected {expected}.".format(got=type(feat_val), expected=feat_desc['type']))
        if feat_desc['edit'] != 'y':
            return ReadOnlyFeatureError("Feature '{}' cannot be modified.".format(feat_name))
        if type(feat_val) == bool:
            return True # No need to check value range
        current_value = getattr(self, 'get_{}'.format(feat_name))()
        
        # Debug
        # print(current_value)
        # print(feat_desc)
        
        if feat_desc['range'][0] == FileDefined:
            if current_value > feat_val:
                return MinimumExceededError("Feature '{feat}' value minimum is {min}, got {got}.".format(feat=feat_name, min=current_value, got=feat_val))
        elif feat_desc['range'][0] > feat_val:
            return MinimumExceededError("Feature '{feat}' value minimum is {min}, got {got}.".format(feat=feat_name, min=feat_desc['range'][0], got=feat_val))
        
        if feat_desc['range'][1] == FileDefined:
            if current_value < feat_val:
                return MaximumExceededError("Feature '{feat}' value maximum is {max}, got {got}.".format(feat=feat_name, max=current_value, got=feat_val))
        elif feat_desc['range'][1] < feat_val:
            return MaximumExceededError("Feature '{feat}' value maximum is {max}, got {got}.".format(feat=feat_name, max=feat_desc['range'][1], got=feat_val))
        return True
    
    def modify_file(self, features, dir='/tmp', verbose=False):
        '''
        Makes a new PDF file with the specified features modified, if 
        possible. 
        
            features: a vector of desired features or a dictionary with feature 
                      names mapped to desired values. 
            verbose: prints a lot if True
        
        Currently, these 68 features are modifiable: 
        
          -- FREELY MODIFIABLE (within bounds) [35 features]: 
            - version
            - {metadata}_{i} where metadata is one of [author, creator, 
              keywords, producer, subject, title] and i is one of [uc, lc, 
              num, oth, dot]. 6 x 5 = 30 features
            - moddate_(ts|tz), createdate_(ts|tz); 4 features
              
          -- INCREMENTABLE ONLY [33 features]: 
            - _incrementable_feats, 32 features
            - size
        
        Returns a dictionary like this:
        {
            'path' : Path to the newly-created PDF with modified features
            'report' : A dictionary with the results of modification attempts 
                       for every feature for which modification was requested. 
                       It maps the feature name to a dictionary: 
                       {
                           'succes' : boolean, indicating modification success
                           'val' : the value which ended up in the file 
                        }
            'feats' : A numpy feature vector of the newly-created PDF file. 
        }
        '''
        if type(features) == numpy.ndarray:                                         # This section creates a
            new_feats = []                                                          # new feature dictionary
            for i in range(0, FeatureDescriptor.get_feature_count()):               # starting from a numpy
                t = FeatureDescriptor.get_feature_description(i)['type']            # array (assumes ordered)
                if t == int:
                    new_feats.append(int(round(features[i])))
                elif t == bool:
                    new_feats.append(False if abs(features[i]) < 0.01 else True)
                elif t == float:
                    new_feats.append(float(features[i]))
            features = new_feats
        if type(features) == list:
            features = dict(zip(FeatureDescriptor.get_feature_names(), features))
        assert type(features) == dict                                               # Up to here
        # Generate a new PDF file
        newpdf = tempfile.NamedTemporaryFile(
            # mode='rwb+',  # Original
            mode='w+b',     # New
            # bufsize=10*1024*1024,  # Original
            # suffix='.pdf',  # Original
            suffix=hashlib.md5(str(time.time()).encode('utf-8')).hexdigest() + '.pdf',
            delete=False,
            dir=dir,
        )
        
        # Copy the old one into the new one
        with open(self.pdf, 'rb') as oldpdf:
            oldbytes = oldpdf.read(1024)
            while oldbytes:
                newpdf.write(oldbytes)
                oldbytes = oldpdf.read(1024)
        
        # Flush the file, so that the changes are visible when we mmap() it
        newpdf.flush()
        
        # Map the file into memory for regular expression support
        ORIGINAL_SIZE = os.path.getsize(newpdf.name)
        mm = mmap.mmap(newpdf.fileno(), ORIGINAL_SIZE, access=mmap.ACCESS_WRITE)
        
        # Reset insert offset
        self.insert_offset = self._get_startxref_position()
        report = {}
        to_change = {} # features with required new values
        features_current = self.retrieve_feature_dictionary()
        
        # Check which of the requested features we can modify
        for (feat, feat_val) in iter(sorted(features.items())):
            if features_current[feat] != feat_val and not isinstance(feat_val, Exception):
                if type(feat_val) == float and abs(features_current[feat] - feat_val) < 1e-6:
                    pass
                else:
                    valid = self.check_feature_change_valid(feat, feat_val)
                    if valid == True:
                        # Modify this feature
                        # Original
                        # if verbose: print "Feature '%s' has to be changed from %s to %s" % (feat, features_current[feat], feat_val)
                        # New
                        if verbose: print("Feature '%s' has to be changed from %s to %s" % (feat, features_current[feat], feat_val))
                        to_change[feat] = feat_val
                    else:
                        # Do not attempt invalid modification
                        # Original
                        # if verbose: print "Attempting to change feature {0} from {1} to {2}".format(feat, features_current[feat], feat_val)
                        # if verbose: print "Feature '%s' failed: %s" % (feat, valid)
                        # New
                        if verbose: print("Attempting to change feature {0} from {1} to {2}".format(feat, features_current[feat], feat_val))
                        if verbose: print("Feature '%s' failed: %s" % (feat, valid))
                        report[feat] = valid
            else:
                # Ignore features which already have the desired values
                # report[feat] = feat_val
                pass
        # This step created two dictionaries, to_change and report, which respectively map
        # each feature to its new value and whether it is possible to apply the change.

        # Modify version
        if 'version' in to_change:
            match = _regex_pdf_version.search(mm)
            if match != None:
                # Original
                # if verbose: print 'Writing %s to mm[%d]' % (str(to_change['version']), match.start(1))
                # mm[match.start(1)] = str(to_change['version'])
                # New
                if verbose: print('Writing %s to mm[%d]' % (str(to_change['version']), match.start(1)))
                mm[match.start(1)] = int(to_change['version'])

                report['version'] = to_change['version']
                if verbose: print('Written {} '.format(mm[7]))
                del to_change['version']
        # This modification happens in place without adding extra bytes to the file
        
        # Modify incrementable features
        for feat in _incrementable_feats:
            if feat in to_change:
                new_val = to_change[feat]
                increase = new_val - features_current[feat]
                # Original
                # if verbose: print "Inserting '%s'*%d" % (_incrementable_feats[feat], increase)
                # New
                if verbose: print("Inserting '%s'*%d" % (_incrementable_feats[feat], increase))
                self._insert_into_mmap(mm, ' {}\n'.format(_incrementable_feats[feat]) * increase)
                report[feat] = to_change[feat]
                del to_change[feat]
        # These changes are not in place. They will add bytes to the file.
        
        # Modify metadata features: author, creator, keywords, producer, subject and title
        # Original
        # for (feat_prefix, feat_str) in _metadata_feats.iteritems():
        # New
        for (feat_prefix, feat_str) in _metadata_feats.items():  # feat_str is the actual string in the file representing the modified field
            # Gather all incrementable metadata features with the given prefix
            metadata_feats = [f[len(feat_prefix) + 1:] for f in to_change if f.startswith(feat_prefix) and not f.endswith(('mismatch', 'len'))]
            # metadata_feats now contains the list of suffixes of the features to modify
            addendum = ''
            # Insert the required characters
            for feat_suffix in metadata_feats:  # This loop creates a
                feat = '{pre}_{suf}'.format(pre=feat_prefix, suf=feat_suffix)
                if feat_suffix == 'lc':
                    addendum += 'a' * (to_change[feat])
                elif feat_suffix == 'uc':
                    addendum += 'Z' * (to_change[feat])
                elif feat_suffix == 'num':
                    addendum += '3' * (to_change[feat])
                elif feat_suffix == 'oth':
                    addendum += '-' * (to_change[feat])
                elif feat_suffix == 'dot':
                    addendum += '.' * (to_change[feat])
                report[feat] = to_change[feat]
                del to_change[feat]
            # Write the formatted feature into the PDF file
            if addendum:
                # Original
                # if verbose: print "Inserting '%s'" % feat_str.format(addendum)
                # New
                if verbose: print("Inserting '%s'" % feat_str.format(addendum))
                self._insert_into_mmap(mm, feat_str.format(addendum))
        # These modifications are not in place. They will add bytes to the file.
        
        # Modify modification timestamp and/or timezone
        if 'moddate_ts' in to_change or 'moddate_tz' in to_change:
            moddate = '/ModDate(D:{ts}{tz})'
            # New
            # moddate = '/ModDate (D:{ts}{tz})'
            # There seem to be a difference in some (newer) PDFs,
            # there is a space after /ModDate before the parenthesis

            ts_str = '{a.tm_year:0>4}{a.tm_mon:0>2}{a.tm_mday:0>2}{a.tm_hour:0>2}{a.tm_min:0>2}{a.tm_sec:0>2}'
            if 'moddate_ts' in to_change:
                ts_str = ts_str.format(a=time.gmtime(to_change['moddate_ts']))
                report['moddate_ts'] = to_change['moddate_ts']
                del to_change['moddate_ts']
            else:
                ts_str = ts_str.format(a=time.gmtime(self.get_moddate_ts()))
            tz_str = "{sign}{h:0>2}'{m:0>2}"
            if 'moddate_tz' in to_change:
                new_tz = to_change['moddate_tz']
                if new_tz == 0:
                    tz_str = 'Z'
                else:
                    tz_str = tz_str.format(sign = '+' if new_tz > 0 else '-', h = abs(new_tz) / 3600, m = (abs(new_tz) % 3600) / 60)
                report['moddate_tz'] = to_change['moddate_tz']
                del to_change['moddate_tz']
            else:
                tz_str = 'Z'
                old_tz = self.get_moddate_tz()
                if old_tz != 0:
                    tz_str = "{sign}{h:0>2}'{m:0>2}".format(sign = '+' if old_tz > 0 else '-', h = abs(old_tz) / 3600, m = (abs(old_tz) % 3600) / 60)
            # Check if there already exists a moddate which can be modified in-place
            datelines = _perl_regex(r'print @-[1], " ", $1 while /\/ModDate\((.*?)\)/g', self.pdf).splitlines()
            modified = False
            if datelines:
                # Original
                # datelines = datelines[-1].split(' ')
                # New
                datelines = datelines[-1].split(b' ')
                mod_location = int(datelines[0])
                old_moddate = datelines[1]
                new_moddate = 'D:{ts}{tz}'.format(ts = ts_str, tz=tz_str)
                if len(new_moddate) == len(old_moddate):
                    # Original
                    # if verbose: print 'Changing "%s" to "%s"' % (old_moddate, new_moddate)
                    # New
                    if verbose: print('Changing "%s" to "%s"' % (old_moddate, new_moddate))
                    mm.seek(mod_location)
                    mm.write(new_moddate)
                    modified = True
            if not modified:
                # Insert a new moddate
                # Original
                # if verbose: print 'Inserting "%s"' % moddate.format(ts = ts_str, tz=tz_str)
                # New
                if verbose: print('Inserting "%s"' % moddate.format(ts = ts_str, tz=tz_str))
                self._insert_into_mmap(mm, moddate.format(ts = ts_str, tz=tz_str))
            
        
        # Modify creation timestamp and/or timezone
        if 'createdate_ts' in to_change or 'createdate_tz' in to_change:
            createdate = '<xap:CreateDate>{ts}{tz}</xap:CreateDate>'
            ts_str = '{a.tm_year:0>4}-{a.tm_mon:0>2}-{a.tm_mday:0>2}T{a.tm_hour:0>2}:{a.tm_min:0>2}:{a.tm_sec:0>2}'
            if 'createdate_ts' in to_change:
                ts_str = ts_str.format(a=time.gmtime(to_change['createdate_ts']))
                report['createdate_ts'] = to_change['createdate_ts']
                del to_change['createdate_ts']
            else:
                ts_str = ts_str.format(a=time.gmtime(self.get_moddate_ts()))
            tz_str = "{sign}{h:0>2}:{m:0>2}"
            if 'createdate_tz' in to_change:
                new_tz = to_change['createdate_tz']
                if new_tz == 0:
                    tz_str = 'Z'
                else:
                    tz_str = tz_str.format(sign = '+' if new_tz > 0 else '-', h = abs(new_tz) / 3600, m = (abs(new_tz) % 3600) / 60)
                report['createdate_tz'] = to_change['createdate_tz']
                del to_change['createdate_tz']
            else:
                tz_str = 'Z'
                old_tz = self.get_createdate_tz()
                if old_tz != 0:
                    tz_str = "{sign}{h:0>2}'{m:0>2}".format(sign = '+' if old_tz > 0 else '-', h = abs(old_tz) / 3600, m = (abs(old_tz) % 3600) / 60)
            # Check if there already exists a moddate which can be modified in-place
            datelines = _perl_regex(r'print @-[1], " ", $1 while /<x[am]p:CreateDate>(.*?)<\/x[am]p:CreateDate>/g', self.pdf).splitlines()
            modified = False
            if datelines:
                # Original
                # datelines = datelines[-1].split(' ')
                # New
                datelines = datelines[-1].split(b' ')
                mod_location = int(datelines[0])
                old_createdate = datelines[1]
                new_createdate = '{ts}{tz}'.format(ts = ts_str, tz=tz_str)
                if len(new_createdate) == len(old_createdate):
                    # Original
                    # if verbose: print 'Changing "%s" to "%s"' % (old_createdate, new_createdate)
                    # New
                    if verbose: print('Changing "%s" to "%s"' % (old_createdate, new_createdate))
                    mm.seek(mod_location)
                    mm.write(new_createdate)
                    modified = True
            if not modified:
                # Original
                # if verbose: print 'Inserting "%s"' % createdate.format(ts = ts_str, tz=tz_str)
                # New
                if verbose: print('Inserting "%s"' % createdate.format(ts = ts_str, tz=tz_str))
                self._insert_into_mmap(mm, createdate.format(ts = ts_str, tz=tz_str))
        
        # Modify size by inserting spaces. Make sure this one comes last
        if 'size' in to_change:
            insert_count = to_change['size'] - mm.size()
            if insert_count > 0:
                # Original
                # if verbose: print 'Modifying size by inserting {} bytes'.format(insert_count)
                # New
                if verbose: print('Modifying size by inserting {} bytes'.format(insert_count))
                self._insert_into_mmap(mm, ' ' * insert_count)
                report['size'] = to_change['size']
                del to_change['size']
            else:
                # Original
                # if verbose: print 'Not modifying size [{} extra bytes already]'.format(-insert_count)
                # New
                if verbose: print('Not modifying size [{} extra bytes already]'.format(-insert_count))
        
        # Flush the memory-mapped file to save changes and close it
        mm.flush()
        mm.close()
        newpdf.close()
        # Original
        # if verbose: print 'Report: %s' % report
        # New
        if verbose: print('Report: %s' % report)
        if to_change and verbose:
            # Original
            # print 'Some features left unmodified (not implemented): %s' % to_change
            # New
            print('Some features left unmodified (not implemented): %s' % to_change)
        # Original
        # if verbose: print 'File: %s' % newpdf.name
        # New
        if verbose: print('File: %s' % newpdf.name)
        for k in report.keys():
            if isinstance(report[k], Exception):
                report[k] = {'success':False, 'val':report[k]}
            else:
                report[k] = {'success':True, 'val':report[k]}
        for k in to_change.keys():
            report[k] = {'success':False, 'val':to_change[k]}
        return {'path' : newpdf.name, 'report' : report, 'feats' : FeatureEdit(newpdf.name).retrieve_feature_vector_numpy()}

    # This function insert the actual bytes inside the PDF file.
    # First it finds the position of the unused space at the end of the file,
    # then it resizes the file to allocate space. It then moves the content
    # at the old insert offset position, to a new place. Finally it copies
    # the new filed inside and updates the insert offset.
    def _insert_into_mmap(self, mmap, data):
        file_trailer = mmap.size() - self.insert_offset
        # New
        data = data.encode()  # Need to know how many bytes will be added

        # Debug
        # print('final size', mmap.size() + len(data))

        mmap.resize(mmap.size() + len(data))
        mmap.move(self.insert_offset + len(data), self.insert_offset, file_trailer)
        mmap.seek(self.insert_offset)
        mmap.write(data)
        self.insert_offset += len(data)
