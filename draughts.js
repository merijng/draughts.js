'use strict'

/*
||==================================================================================
|| DESCRIPTION OF IMPLEMENTATION PRINCIPLES
|| A. Position for rules (internal representation): string with length 56.
||    Special numbering for easy applying rules.
||    Valid characters: b B w W 0 -
||       b (black) B (black king) w (white) W (white king) 0 (empty) (- unused)
||    Examples:
||      '-bbbBBB000w-wwWWWwwwww-bbbbbbbbbb-000wwwwwww-00bbbwwWW0-'
||      '-0000000000-0000000000-0000000000-0000000000-0000000000-'  (empty position)
||      '-bbbbbbbbbb-bbbbbbbbbb-0000000000-wwwwwwwwww-wwwwwwwwww-'  (start position)
|| B. Position (external respresentation): string with length 51.
||    Square numbers are represented by the position of the characters.
||    Position 0 is reserved for the side to move (B or W)
||    Valid characters: b B w W 0
||       b (black) B (black king) w (white) W (white king) 0 (empty)
||    Examples:
||       'B00000000000000000000000000000000000000000000000000'  (empty position)
||       'Wbbbbbbbbbbbbbbbbbbbb0000000000wwwwwwwwwwwwwwwwwwww'  (start position)
||       'WbbbbbbBbbbbb00bbbbb000000w0W00ww00wwwwww0wwwwwwwww'  (random position)
||
|| External numbering      Internal Numbering
|| --------------------    --------------------
||   01  02  03  04  05      01  02  03  04  05
|| 06  07  08  09  10      06  07  08  09  10
||   11  12  13  14  15      12  13  14  15  16
|| 16  17  18  19  20      17  18  19  20  21
||   21  22  23  24  25      23  24  25  26  27
|| 26  27  28  29  30      28  29  30  31  32
||   31  32  33  34  35      34  35  36  37  38
|| 36  37  38  39  40      39  40  41  42  43
||   41  42  43  44  45      45  46  47  48  49
|| 46  47  48  49  50      50  51  52  53  54
|| --------------------    --------------------
||
|| Internal numbering has fixed direction increments for easy applying rules:
||   NW   NE         -5   -6
||     \ /             \ /
||     sQr     >>      sQr
||     / \             / \
||   SW   SE         +5   +6
||
|| DIRECTION-STRINGS
|| Strings of variable length for each of four directions at one square.
|| Each string represents the position in that direction.
|| Directions: NE, SE, SW, NW (wind directions)
|| Example for square 29 (internal number):
||   NE: 29, 24, 19, 14, 09, 04     b00bb0
||   SE: 35, 41, 47, 53             bww0
||   SW: 34, 39                     b0
||   NW: 23, 17                     bw
|| CONVERSION internal to external representation of numbers.
||   N: external number, values 1..50
||   M: internal number, values 0..55 (invalid 0,11,22,33,44,55)
||   Formulas:
||   M = N + floor((N-1)/10)
||   N = M - floor((M-1)/11)
||
||==================================================================================
*/
var Draughts = function (fen) {
  var BLACK = 'B'
  var WHITE = 'W'
  // var EMPTY = -1
  var MAN = 'b'
  var KING = 'w'
  var SYMBOLS = 'bwBW'
  var DEFAULT_FEN = 'W:W31-50:B1-20'
  var position
  var DEFAULT_POSITION_INTERNAL = '-bbbbbbbbbb-bbbbbbbbbb-0000000000-wwwwwwwwww-wwwwwwwwww-'
  var DEFAULT_POSITION_EXTERNAL = 'Wbbbbbbbbbbbbbbbbbbbb0000000000wwwwwwwwwwwwwwwwwwww'
  var STEPS = {NE: -5, SE: 6, SW: 5, NW: -6}
  var POSSIBLE_RESULTS = ['2-0', '0-2', '1-1', '0-0', '*', '1-0', '0-1']
  var FLAGS = {
    NORMAL: 'n',
    CAPTURE: 'c',
    PROMOTION: 'p'
  }

  var UNICODES = {
    'w': '\u26C0',
    'b': '\u26C2',
    'B': '\u26C3',
    'W': '\u26C1',
    '0': '\u0020\u0020'
  }

  var SIGNS = {
    n: '-',
    c: 'x'
  }
  var BITS = {
    NORMAL: 1,
    CAPTURE: 2,
    PROMOTION: 4
  }

  var turn = WHITE
  var history = []
  var header = {}

  if (!fen) {
    position = DEFAULT_POSITION_INTERNAL
    load(DEFAULT_FEN)
  } else {
    position = DEFAULT_POSITION_INTERNAL
    load(fen)
  }

  function clear () {
    position = DEFAULT_POSITION_INTERNAL
    turn = WHITE
    history = []
    header = {}
    update_setup(generate_fen())
  }

  function reset () {
    load(DEFAULT_FEN)
  }

  function load (fen, validate = true) {
    // TODO for default fen
    if (!fen || fen === DEFAULT_FEN) {
      position = DEFAULT_POSITION_INTERNAL
      update_setup(generate_fen(position))
      return true
    }
    // fen_constants(dimension) //TODO for empty fens

    if(validate)
    {
      var checkedFen = validate_fen(fen)
      if (!checkedFen.valid) {
        console.error('Fen Error', fen, checkedFen)
        return false
      }
    }

    clear()

    // remove spaces
    fen = fen.replace(/\s+/g, '')
    // remove suffixes
    fen.replace(/\..*$/, '')

    var tokens = fen.split(':')
    // which side to move
    turn = tokens[0].substr(0, 1)

    // var positions = new Array()
    var externalPosition = DEFAULT_POSITION_EXTERNAL
    for (var i = 1; i <= externalPosition.length; i++) {
      externalPosition = setCharAt(externalPosition, i, 0)
    }
    externalPosition = setCharAt(externalPosition, 0, turn)
    // TODO refactor
    for (var k = 1; k <= 2; k++) {
      // TODO called twice
      var color = tokens[k].substr(0, 1)
      var sideString = tokens[k].substr(1)
      if (sideString.length === 0) continue
      var numbers = sideString.split(',')
      for (i = 0; i < numbers.length; i++) {
        var numSquare = numbers[i]
        var isKing = (numSquare.substr(0, 1) === 'K')
        numSquare = (isKing === true ? numSquare.substr(1) : numSquare) // strip K
        var range = numSquare.split('-')
        if (range.length === 2) {
          var from = parseInt(range[0], 10)
          var to = parseInt(range[1], 10)
          for (var j = from; j <= to; j++) {
            externalPosition = setCharAt(externalPosition, j, (isKing === true ? color.toUpperCase() : color.toLowerCase()))
          }
        } else {
          numSquare = parseInt(numSquare, 10)
          externalPosition = setCharAt(externalPosition, numSquare, (isKing === true ? color.toUpperCase() : color.toLowerCase()))
        }
      }
    }

    position = convertPosition(externalPosition, 'internal')
    update_setup(generate_fen(position))

    return true
  }

  function validate_fen (fen) {
    var errors = [
      {
        code: 0,
        message: 'no errors'
      },
      {
        code: 1,
        message: 'fen position not a string'
      },
      {
        code: 2,
        message: 'fen position has not colon at second position'
      },
      {
        code: 3,
        message: 'fen position has not 2 colons'
      },
      {
        code: 4,
        message: 'side to move of fen position not valid'
      },
      {
        code: 5,
        message: 'color(s) of sides of fen position not valid'
      },
      {
        code: 6,
        message: 'squares of fen position not integer'
      },
      {
        code: 7,
        message: 'squares of fen position not valid'
      },
      {
        code: 8,
        message: 'empty fen position'
      }
    ]

    if (typeof fen !== 'string') {
      return {valid: false, error: errors[0], fen: fen}
    }

    fen = fen.replace(/\s+/g, '')

    if (fen === 'B::' || fen === 'W::' || fen === '?::') {
      return {valid: true, fen: fen + ':B:W'} // exception allowed i.e. empty fen
    }
    fen = fen.trim()
    fen = fen.replace(/\..*$/, '')

    if (fen === '') {
      return {valid: false, error: errors[7], fen: fen}
    }

    if (fen.substr(1, 1) !== ':') {
      return {valid: false, error: errors[1], fen: fen}
    }

    // fen should be 3 sections separated by colons
    var parts = fen.split(':')
    if (parts.length !== 3) {
      return {valid: false, error: errors[2], fen: fen}
    }

    //  which side to move
    var turnColor = parts[0]
    if (turnColor !== 'B' && turnColor !== 'W' && turnColor !== '?') {
      return {valid: false, error: errors[3], fen: fen}
    }

    // check colors of both sides
    var colors = parts[1].substr(0, 1) + parts[2].substr(0, 1)
    if (colors !== 'BW' && colors !== 'WB') {
      return {valid: false, error: errors[4], fen: fen}
    }

    // check parts for both sides
    for (var k = 1; k <= 2; k += 1) {
      var sideString = parts[k].substr(1) // Stripping color
      if (sideString.length === 0) {
        continue
      }
      var numbers = sideString.split(',')
      for (var i = 0; i < numbers.length; i++) {
        var numSquare = numbers[i]
        var isKing = (numSquare.substr(0, 1) === 'K')
        numSquare = (isKing === true ? numSquare.substr(1) : numSquare)
        var range = numSquare.split('-')
        if (range.length === 2) {
          if (isInteger(range[0]) === false) {
            return {valid: false, error: errors[5], fen: fen, range: range[0]}
          }
          if (!(range[0] >= 1 && range[0] <= 100)) {
            return {valid: false, error: errors[6], fen: fen}
          }
          if (isInteger(range[1]) === false) {
            return {valid: false, error: errors[5], fen: fen}
          }
          if (!(range[1] >= 1 && range[1] <= 100)) {
            return {valid: false, error: errors[6], fen: fen}
          }
        } else {
          if (isInteger(numSquare) === false) {
            return {valid: false, error: errors[5], fen: fen}
          }
          if (!(numSquare >= 1 && numSquare <= 100)) {
            return {valid: false, error: errors[6], fen: fen}
          }
        }
      }
    }

    return {valid: true, error_number: 0, error: errors[0]}
  }

  function generate_fen () {
    var black = []
    var white = []
    var externalPosition = convertPosition(position, 'external')
    for (var i = 0; i < externalPosition.length; i++) {
      switch (externalPosition[i]) {
        case 'w':
          white.push(i)
          break
        case 'W':
          white.push('K' + i)
          break
        case 'b':
          black.push(i)
          break
        case 'B':
          black.push('K' + i)
          break
        default:
          break
      }
    }
    return turn.toUpperCase() + ':W' + white.join(',') + ':B' + black.join(',')
  }

  function generatePDN (options) {
    // for html usage {maxWidth: 72, newline_char: "<br />"}
    var newline = (typeof options === 'object' && typeof options.newline_char === 'string')
      ? options.newline_char : '\n'
    var maxWidth = (typeof options === 'object' && typeof options.maxWidth === 'number')
      ? options.maxWidth : 0
    var result = []
    var headerExists = false

    for (var i in header) {
      result.push('[' + i + ' "' + header[i] + '"]' + newline)
      headerExists = true
    }

    if (headerExists && history.length) {
      result.push(newline)
    }

    var tempHistory = clone(history)

    var moves = []
    var moveString = ''

    while (tempHistory.length > 0) {
      var move = tempHistory.shift()
      if (move.turn === 'W') {
        moveString += 0 + '. '
      }
      moveString += move.move.from
      if (move.move.flags === 'c') {
        moveString += 'x'
      } else {
        moveString += '-'
      }
      moveString += move.move.to
      moveString += ' '
    }

    if (moveString.length) {
      moves.push(moveString)
    }

    // TODO resutl from pdn or header??
    if (typeof header.Result !== 'undefined') {
      moves.push(header.Result)
    }

    if (maxWidth === 0) {
      return result.join('') + moves.join(' ')
    }

    var currentWidth = 0
    for (i = 0; i < moves.length; i++) {
      if (currentWidth + moves[i].length > maxWidth && i !== 0) {
        if (result[result.length - 1] === ' ') {
          result.pop()
        }

        result.push(newline)
        currentWidth = 0
      } else if (i !== 0) {
        result.push(' ')
        currentWidth++
      }
      result.push(' ')
      currentWidth += moves[i].length
    }

    return result.join('')
  }

  function set_header (args) {
    for (var i = 0; i < args.length; i += 2) {
      if (typeof args[i] === 'string' && typeof args[i + 1] === 'string') {
        header[args[i]] = args[i + 1]
      }
    }
    return header
  }

  /* called when the initial board setup is changed with put() or remove().
   * modifies the SetUp and FEN properties of the header object.  if the FEN is
   * equal to the default position, the SetUp and FEN are deleted
   * the setup is only updated if history.length is zero, ie moves haven't been
   * made.
   */
  function update_setup (fen) {
    if (history.length > 0) {
      return false
    }
    if (fen !== DEFAULT_FEN) {
      header['SetUp'] = '1'
      header['FEN'] = fen
    } else {
      delete header['SetUp']
      delete header['FEN']
    }
  }

  function parsePDN (pdn, options) {
    var newline_char = (typeof options === 'object' &&
    typeof options.newline_char === 'string')
      ? options.newline_char : '\r?\n'
    var regex = new RegExp('^(\\[(.|' + mask(newline_char) + ')*\\])' +
      '(' + mask(newline_char) + ')*' +
      '1.(' + mask(newline_char) + '|.)*$', 'g')

    function mask (str) {
      return str.replace(/\\/g, '\\')
    }

    function parsePDNHeader (header, options) {
      var headerObj = {}
      var headers = header.split(new RegExp(mask(newline_char)))
      var key = ''
      var value = ''

      for (var i = 0; i < headers.length; i++) {
        key = headers[i].replace(/^\[([A-Z][A-Za-z]*)\s.*\]$/, '$1')
        value = headers[i].replace(/^\[[A-Za-z]+\s"(.*)"\]$/, '$1')
        if (trim(key).length > 0) {
          headerObj[key] = value
        }
      }

      return headerObj
    }

    var headerString = pdn.replace(regex, '$1')
    if (headerString[0] !== '[') {
      headerString = ''
    }

    reset()

    var headers = parsePDNHeader(headerString, options)

    for (var key in headers) {
      set_header([key, headers[key]])
    }

    if (headers['Setup'] === '1') {
      if (!(('FEN' in headers) && load(headers['FEN']))) {
        console.error('fen invalid')
        return false
      }
    } else {
      position = DEFAULT_POSITION_INTERNAL
    }

    /* delete header to get the moves */
    var ms = pdn.replace(headerString, '').replace(new RegExp(mask(newline_char), 'g'), ' ')

    /* delete comments */
    ms = ms.replace(/(\{[^}]+\})+?/g, '')

    /* delete recursive annotation variations */
    var rav_regex = /(\([^\(\)]+\))+?/g
    while (rav_regex.test(ms)) {
      ms = ms.replace(rav_regex, '')
    }

    /* delete move numbers */
    // TODO not working for move numbers with space
    ms = ms.replace(/\d+\./g, '')

    /* delete ... indicating black to move */
    ms = ms.replace(/\.\.\./g, '')

    /* trim and get array of moves */
    var moves = trim(ms).split(new RegExp(/\s+/))

    /* delete empty entries */
    moves = moves.join(',').replace(/,,+/g, ',').split(',')

    var move = ''
    for (var half_move = 0; half_move < moves.length - 1; half_move += 1) {
      move = getMoveObject(moves[half_move])
      if (!move) {
        return false
      } else {
        makeMove(move)
      }
    }

    var result = moves[moves.length - 1]
    if (POSSIBLE_RESULTS.indexOf(result) > -1) {
      if (headers['Result'] === 'undefined') {
        set_header(['Result', result])
      }
    } else {
      move = getMoveObject(result)
      if (!move) {
        return false
      } else {
        makeMove(move)
      }
    }
    return true
  }

  function getMoveObject (move) {
    // TODO move flags for both capture and promote??
    var tempMove = {}
    var matches = move.split(/[x|-]/)
    tempMove.from = parseInt(matches[0], 10)
    tempMove.to = parseInt(matches[1], 10)
    var moveType = move.match(/[x|-]/)[0]
    if (moveType === '-') {
      tempMove.flags = FLAGS.NORMAL
    } else {
      tempMove.flags = FLAGS.CAPTURE
    }
    tempMove.piece = position.charAt(convertNrInternal(tempMove.from))
    var moves = getLegalMoves(tempMove.from);
    convertMoves(moves, 'external');
    // if move legal then make move
    for (var i = 0; i < moves.length; i += 1) {
      if (tempMove.to === moves[i].to && tempMove.from === moves[i].from) {
        if (moves[i].takes.length > 0) {
          tempMove.flags = FLAGS.CAPTURE
          tempMove.captures = moves[i].takes
          tempMove.takes = moves[i].takes
        }
        return tempMove
      }
    }
    return false
  }

  // TODO: Is it the effort to create a flow without converts for 'AI performance' perposes?
  function makeMove (move) {
    move.piece = position.charAt(convertNrInternal(move.from))
    position = setCharAt(position, convertNrInternal(move.to), move.piece)
    position = setCharAt(position, convertNrInternal(move.from), 0)
    move.flags = FLAGS.NORMAL

    if (move.takes && move.takes.length) {
      move.flags = FLAGS.CAPTURE

      var i = move.takes.length;
      while(i--) position = setCharAt(position, convertNrInternal(move.takes[i]), 0)
    }
    
    // Promoting piece here
    if (move.to <= 5 && move.piece === 'w') {
      move.flags = FLAGS.PROMOTION
      position = setCharAt(position, convertNrInternal(move.to), move.piece.toUpperCase())
    } else if (move.to >= 46 && move.piece === 'b') {
      position = setCharAt(position, convertNrInternal(move.to), move.piece.toUpperCase())
    }

    push(move)
    turn = swapColor(turn)
  }

  function get (square) {
    return position.charAt(convertNrInternal(square))
  }

  function put (piece, square) {
    // check for valid piece string
    if (SYMBOLS.match(piece) === null) {
      return false
    }

    // check for valid square
    if (outsideBoard(convertNrInternal(square)) === true) {
      return false
    }
    position = setCharAt(position, convertNrInternal(square), piece)
    update_setup(generate_fen())

    return true
  }

  function remove (square) {
    position = setCharAt(position, convertNrInternal(square), 0)
    update_setup(generate_fen())

    return get(square)
  }

  function generate_moves (square) {
    var moves = []

    if (square) {
      moves = getLegalMoves(square.square)
    } else {
      var tempCaptures = getCaptures()
      // TODO change to be applicable to array
      if (tempCaptures.length) {
        var i = tempCaptures.length;
        while(i--)
        {
          tempCaptures[i].flags = FLAGS.CAPTURE
          tempCaptures[i].captures = tempCaptures[i].jumps
        }

        return tempCaptures
      }
      moves = getMoves()
    }
    // TODO returns [] for on hovering for square no
    moves = [].concat.apply([], moves)
    return moves
  }

  function getLegalMoves (index) {
    var legalMoves
    index = parseInt(index, 10);
    if (!Number.isNaN(index)) {
      index = convertNrInternal(index)

      var captures = capturesAtSquare(index, {position: position, dirFrom: ''}, {jumps: [index], takes: [], piecesTaken: []})

      captures = longestCapture(captures)
      legalMoves = captures
      if (captures.length === 0) {
        legalMoves = movesAtSquare(index)
      }
    }
    // TODO called on hover ??
    convertMoves(legalMoves, 'external');

    return legalMoves;
  }

  function getMoves () {
    var moves = []

    for (var i = 1; i < position.length; i++) {
      if (position[i] === turn || position[i] === turn.toLowerCase()) {
        var tempMoves = movesAtSquare(i)
        if (tempMoves.length) {
          convertMoves(tempMoves, 'external');
          moves = moves.concat(tempMoves)
        }
      }
    }
    return moves
  }

  function setCharAt (position, idx, chr) {
    idx = parseInt(idx, 10)

    if (idx > position.length - 1)
      return position.toString()

    return position.substr(0, idx) + chr + position.substr(idx + 1)
  }

  function movesAtSquare (square) {
    var moves = []
    var posFrom = square
    var piece = position.charAt(posFrom)

    switch (piece) {
      case 'b':
      case 'w':
        var dirStrings = directionStrings(position, posFrom, 2)
        for (var dir in dirStrings) {
          var matchArray = dirStrings[dir].match(/^[bw]0/) // e.g. b0 w0
          if (matchArray !== null && validDir(piece, dir) === true) {
            var posTo = posFrom + STEPS[dir]
            moves.push({from: posFrom, to: posTo, takes: [], jumps: []})
          }
        }
        break
      case 'W':
      case 'B':
        var dirStrings = directionStrings(position, posFrom, 2)
        for (dir in dirStrings) {
          matchArray = dirStrings[dir].match(/^[BW]0+/) // e.g. B000, W0
          if (matchArray !== null && validDir(piece, dir) === true) {
            for (var i = 0; i < matchArray[0].length; i++) {
              posTo = posFrom + (i * STEPS[dir])
              moves.push({from: posFrom, to: posTo, takes: [], jumps: []})
            }
          }
        }
        break
    }
    return moves
  }

  function getCaptures () {
    var captures = []
    var i = position.length;
    while(i--)
    {
      if (position[i] === turn || position[i] === turn.toLowerCase()) {
        var posFrom = i
        var state = {position: position, dirFrom: ''}
        var capture = {jumps: [], takes: [], from: posFrom, to: '', piecesTaken: []}
        capture.jumps[0] = posFrom
        var tempCaptures = capturesAtSquare(posFrom, state, capture)
        if (tempCaptures.length) {
          convertMoves(tempCaptures, 'external');
          captures = captures.concat(tempCaptures);
        }
      }
    }

    captures = longestCapture(captures)
    return captures
  }

  function capturesAtSquare (posFrom, state, capture) {
    var piece = state.position.charAt(posFrom)
    if (piece !== 'b' && piece !== 'w' && piece !== 'B' && piece !== 'W') {
      return [capture]
    }
    
    var dirs = (piece === 'b' || piece === 'w')
      ? directionStrings(state.position, posFrom, 3)
      : directionStrings(state.position, posFrom);

    var finished = true
    var captureArrayForDir = []
    for (var dir in dirs) {
      if (dir === state.dirFrom) {
        continue
      }
      var str = dirs[dir]
      switch (piece) {
        case 'b':
        case 'w':
          var matchArray = str.match(/^b[wW]0|^w[bB]0/) // matches: bw0, bW0, wB0, wb0
          if (matchArray !== null) {
            var posTo = posFrom + (2 * STEPS[dir])
            var posTake = posFrom + (1 * STEPS[dir])
            if (capture.takes.indexOf(posTake) > -1) {
              continue // capturing twice forbidden
            }
            var updateCapture = clone(capture)
            updateCapture.to = posTo
            updateCapture.jumps.push(posTo)
            updateCapture.takes.push(posTake)
            updateCapture.piecesTaken.push(position.charAt(posTake))
            updateCapture.from = posFrom
            var updateState = clone(state)
            updateState.dirFrom = oppositeDir(dir)
            var pieceCode = updateState.position.charAt(posFrom)
            updateState.position = setCharAt(updateState.position, posFrom, 0)
            updateState.position = setCharAt(updateState.position, posTo, pieceCode)
            finished = false
            captureArrayForDir[dir] = capturesAtSquare(posTo, updateState, updateCapture)
          }
          break
        case 'B':
        case 'W':
          matchArray = str.match(/^B0*[wW]0+|^W0*[bB]0+/) // matches: B00w000, WB00
          if (matchArray !== null) {
            var matchStr = matchArray[0]
            var matchArraySubstr = matchStr.match(/[wW]0+$|[bB]0+$/) // matches: w000, B00
            var matchSubstr = matchArraySubstr[0]
            var takeIndex = matchStr.length - matchSubstr.length
            posTake = posFrom + (takeIndex * STEPS[dir])
            if (capture.takes.indexOf(posTake) > -1) {
              continue
            }
            for (var i = 1; i < matchSubstr.length; i++) {
              posTo = posFrom + ((takeIndex + i) * STEPS[dir])
              updateCapture = clone(capture)
              updateCapture.jumps.push(posTo)
              updateCapture.to = posTo
              updateCapture.takes.push(posTake)
              updateCapture.piecesTaken.push(position.charAt(posTake))
              updateCapture.posFrom = posFrom
              updateState = clone(state)
              updateState.dirFrom = oppositeDir(dir)
              pieceCode = updateState.position.charAt(posFrom)
              updateState.position = setCharAt(updateState.position, posFrom, 0)
              updateState.position = setCharAt(updateState.position, posTo, pieceCode)
              finished = false
              var dirIndex = dir + i.toString()
              captureArrayForDir[dirIndex] = capturesAtSquare(posTo, updateState, updateCapture)
            }
          }
          break
        default:
          captureArrayForDir = []
      }
    }
    var captureArray = []
    if (finished === true && capture.takes.length) {
      // fix for mutiple capture
      capture.from = capture.jumps[0]
      captureArray[0] = capture
    } else {
      for (dir in captureArrayForDir) {
        captureArray = captureArray.concat(captureArrayForDir[dir])
      }
    }
    return captureArray
  }

  function push (move) {
    history.push({
      move: move,
      turn: turn
    })
  }

  function undoMove () {

    var old = history.pop()
    if (!old) return null;

    var oldMove = old.move;
    turn = old.turn

    switch(oldMove.flags)
    {
      case 'n': // Normal move
        position = setCharAt(position, convertNrInternal(oldMove.from), oldMove.piece);
        position = setCharAt(position, convertNrInternal(oldMove.to), 0);
        break;
      case 'p': // Promotion
        position = setCharAt(position, convertNrInternal(oldMove.from), oldMove.piece.toLowerCase());
        position = setCharAt(position, convertNrInternal(oldMove.to), 0);

        var i = oldMove.takes.length;
        while(i--) position = setCharAt(position, convertNrInternal(oldMove.takes[i]), oldMove.piecesTaken[i])
        break;
      case 'c': // Capture
        position = setCharAt(position, convertNrInternal(oldMove.from), oldMove.piece);
        position = setCharAt(position, convertNrInternal(oldMove.to), 0);
        
        var i = oldMove.takes.length;
        while(i--)  position = setCharAt(position, convertNrInternal(oldMove.takes[i]), oldMove.piecesTaken[i])
        break;
    }

    return oldMove
  }

  function swapColor (c) {
    return c === WHITE ? BLACK : WHITE
  }

  function isInteger (int) {
    var regex = /^\d+$/;
    return regex.test(int);
  }

  function longestCapture (captures) {
    var maxJumpCount = 0
    var i = captures.length;
    while(i--)
    {
      if (captures[i].jumps.length > maxJumpCount)
        maxJumpCount = captures[i].jumps.length
    }

    if (maxJumpCount < 2)
      return [];

    var selectedCaptures = [];
    i = captures.length;
    while(i--)
    {
      if (captures[i].jumps.length === maxJumpCount)
        selectedCaptures.push(captures[i])
    }

    return selectedCaptures
  }

  function convertMoves (moves, type) {
    if (!type || moves.length === 0) {
      return tempMoves
    }

    for (var i = 0; i < moves.length; i++) {
      var j = moves[i].jumps.length;
      while(j--) moves[i].jumps[j] = convertNumber(moves[i].jumps[j], type)
      
      j = moves[i].takes.length;
      while(j--) moves[i].takes[j] = convertNumber(moves[i].takes[j], type)
      
      moves[i].from = convertNumber(moves[i].from, type)
      moves[i].to = convertNumber(moves[i].to, type)
    }
  }

  function convertNrInternal (number) {
    var num = parseInt(number, 10);
    return num + ~~((num - 1) / 10);
  }

  function convertNrExternal (number) {
    var num = parseInt(number, 10);
    return num - ~~((num - 1) / 11);
  }

  function convertNumber (number, notation) {
    switch (notation) {
      case 'internal': return convertNrInternal(number)
      case 'external': return convertNrExternal (number)
      default: return parseInt(number, 10);
    }
  }

  function convertPosition (position, notation) {
    var sub1, sub2, sub3, sub4, sub5, newPosition
    switch (notation) {
      case 'internal':
        sub1 = position.substr(1, 10)
        sub2 = position.substr(11, 10)
        sub3 = position.substr(21, 10)
        sub4 = position.substr(31, 10)
        sub5 = position.substr(41, 10)
        newPosition = '-' + sub1 + '-' + sub2 + '-' + sub3 + '-' + sub4 + '-' + sub5 + '-'
        break
      case 'external':
        sub1 = position.substr(1, 10)
        sub2 = position.substr(12, 10)
        sub3 = position.substr(23, 10)
        sub4 = position.substr(34, 10)
        sub5 = position.substr(45, 10)
        newPosition = '?' + sub1 + sub2 + sub3 + sub4 + sub5
        break
      default: newPosition = position
    }
    return newPosition
  }

  function outsideBoard (square) {
    // internal notation only
    var n = parseInt(square, 10);
    return !(n >= 0 && n <= 55 && (n % 11) !== 0);
  }

  /*
    Create direction strings for square at position (internal representation)
    Output object with four directions as properties (four rhumbs).
    Each property has a string as value representing the pieces in that direction.
    Piece of the given square is part of each string.
    Example of output: {NE: 'b0', SE: 'b00wb00', SW: 'bbb00', NW: 'bb'}
  */
  function directionStrings (tempPosition, square, maxLength = 100) {

    var dirStrings = {}
    for (var dir in STEPS) {
      var dirArray = []
      var i = 0
      var index = square
      do {
        dirArray[i] = tempPosition.charAt(index)
        i++
        index = square + i * STEPS[dir]
      } while (outsideBoard(index) === false && i < maxLength)

      dirStrings[dir] = dirArray.join('')
    }

    return dirStrings
  }

  function oppositeDir (direction) {
    var opposite = {NE: 'SW', SE: 'NW', SW: 'NE', NW: 'SE'}
    return opposite[direction]
  }

  function validDir (piece, dir) {
    var validDirs = {
      w: {NE: true, SE: false, SW: false, NW: true},
      b: {NE: false, SE: true, SW: true, NW: false}
    }
    return validDirs[piece.toLowerCase()][dir]
  }

  function ascii (unicode) {
    var extPosition = convertPosition(position, 'external')
    var s = '\n+-------------------------------+\n'
    var i = 1
    for (var row = 1; row <= 10; row++) {
      s += '|\t'
      if (row % 2 !== 0) {
        s += '  '
      }
      for (var col = 1; col <= 10; col++) {
        if (col % 2 === 0) {
          s += '  '
          i++
        } else {
          if (unicode) {
            s += ' ' + UNICODES[extPosition[i]]
          } else {
            s += ' ' + extPosition[i]
          }
        }
      }
      if (row % 2 === 0) {
        s += '  '
      }
      s += '\t|\n'
    }
    s += '+-------------------------------+\n'
    return s
  }

  function gameOver () {
    // First check if any piece left
    for (var i = 0; i < position.length; i++) {
      if (position[i].toLowerCase() === turn.toLowerCase()) {
        // if moves left game not over
        return generate_moves().length === 0
      }
    }
    return true
  }

  function getHistory (options) {
    var tempHistory = clone(history)
    var moveHistory = []
    var verbose = (typeof options !== 'undefined' && 'verbose' in options && options.verbose)
    while (tempHistory.length > 0) {
      var move = tempHistory.shift()
      if (verbose) {
        moveHistory.push(makePretty(move))
      } else {
        moveHistory.push(move.move.from + SIGNS[move.move.flags] + move.move.to)
      }
    }

    return moveHistory
  }

  function getPosition () {
    return convertPosition(position, 'external')
  }

  function makePretty (uglyMove) {
    var move = {}
    move.from = uglyMove.move.from
    move.to = uglyMove.move.to
    move.flags = uglyMove.move.flags
    move.piece = uglyMove.move.piece
    if (move.flags === 'c') {
      move.captures = uglyMove.move.captures.join(',')
    }
    return move
  }

  // TODO: this function copies an object.
  // it is faster then JSON.parse(JSON.stringify(obj))
  // In ES6 there is even a better way. Change it please!
  function clone (obj) {
    var c, i;
  
    if (typeof obj !== 'object' || !obj)
      return obj;
  
    if ('[object Array]' === Object.prototype.toString.apply(obj)) {
      c = [];
      var len = obj.length;
      for (i = 0; i < len; i++)
        c[i] = clone(obj[i]);
      return c;
    }
  
    c = {};
    for (i in obj)
      if (obj.hasOwnProperty(i))
        c[i] = clone(obj[i]);
    return c;
  }

  function trim (str) {
    return str.replace(/^\s+|\s+$/g, '')
  }

  return {
    WHITE: WHITE,
    BLACK: BLACK,
    MAN: MAN,
    KING: KING,
    FLAGS: FLAGS,
    SQUARES: 'A8',

    load: function (fen, validate = true) {
      return load(fen, validate)
    },

    reset: function () {
      return reset()
    },

    moves: generate_moves,

    gameOver: gameOver,

    inDraw: function () {
      return false
    },

    validate_fen: validate_fen,

    fen: generate_fen,

    pdn: generatePDN,

    load_pdn: function (pdn, options) {},

    parsePDN: parsePDN,

    header: function () {
      return set_header(arguments)
    },

    ascii: ascii,

    turn: function () {
      return turn.toLowerCase()
    },

    move: function move (move, validateMove = true) {
      if(!validateMove){
        makeMove(move);
        return move;
      }

      if (typeof move.to === 'undefined' && typeof move.from === 'undefined') {
        return false
      }

      move.to = parseInt(move.to, 10)
      move.from = parseInt(move.from, 10)

      var moves = generate_moves()
      var i = moves.length;
      while(i--)
      {
        if ((move.to === moves[i].to) && (move.from === moves[i].from)) {
          makeMove(moves[i])
          return moves[i]
        }
      }

      return false
    },

    getMoves: getMoves,

    getLegalMoves: getLegalMoves,

    undo: function () {
      return undoMove()
    },

    clear: function () {
      return clear()
    },

    put: function (piece, square) {
      return put(piece, square)
    },

    get: function (square) {
      return get(square)
    },

    remove: function (square) {
      return remove(square)
    },

    history: getHistory,

    convertMoves: convertMoves,

    convertNumber: convertNumber,

    convertPosition: convertPosition,

    outsideBoard: outsideBoard,

    directionStrings: directionStrings,

    oppositeDir: oppositeDir,

    validDir: validDir,

    position: getPosition,

    clone: clone,

    makePretty: makePretty,

    captures: getCaptures
  }
}

if (typeof exports !== 'undefined') {
  exports.Draughts = Draughts
}

if (typeof define !== 'undefined') {
  define(function () {
    return Draughts
  })
}