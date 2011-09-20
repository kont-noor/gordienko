  require 'rubygems'
  require 'sinatra'
  require 'sinatra/content_for'
  require 'erb'
  require 'uri'

#  enable :sessions

class Main < Sinatra::Base

  set :app_file, __FILE__
  set :root, Proc.new { app_file && File.expand_path(File.dirname(app_file)) }
  set :public, Proc.new { root && File.join(root, 'public') }
  set :static, Proc.new { public && File.exist?(public) }
	
  before do
    content_type :html, 'charset' => 'utf-8'
  end

  def with_layout(template, options={}) 
    erb(template, options.merge(:layout => :'/header'))
  end

  get '/' do
    with_layout :'/index'
  end
  
  get '/consultations' do
    with_layout :'/consultations'
  end

  get '/news' do
    with_layout :'/news'
  end

  get '/guest' do
    with_layout :'/guest'
  end

  get '/information' do
    with_layout :'/information'
  end

  get '/contacts' do
    with_layout :'/contacts'
  end

  helpers Sinatra::ContentFor   

end
