require('dotenv').config();

module.exports = {
    PORT: process.env.PORT || 3000,
    UPLOAD_DIR: './uploads'
    // MATHEMATICA_PATH: '/usr/local/bin/wolframscript'
};
